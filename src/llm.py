import openai
import re
import threading
from config import LLMConfig
from abc import ABC, abstractmethod
from typing import Dict, List, Tuple, Any, Optional

# 本地模型缓存：instance_key -> (model, tokenizer)
_local_model_cache: Dict[str, Any] = {}
# 每个本地模型实例独立推理锁：同实例串行、不同实例可并行
_local_model_locks: Dict[str, threading.Lock] = {}
# 保护模型缓存和锁字典
_local_cache_lock = threading.Lock()


def _get_model_lock(instance_key: str) -> threading.Lock:
    with _local_cache_lock:
        lock = _local_model_locks.get(instance_key)
        if lock is None:
            lock = threading.Lock()
            _local_model_locks[instance_key] = lock
        return lock


# 全局 token 统计追踪器
class TokenTracker:
    """全局 token 使用统计追踪器"""
    _instance = None
    _instance_lock = threading.Lock()
    
    def __new__(cls):
        if cls._instance is None:
            with cls._instance_lock:
                if cls._instance is None:
                    cls._instance = super().__new__(cls)
                    cls._instance.stats = {
                        "total_prompt_tokens": 0,
                        "total_completion_tokens": 0,
                        "total_tokens": 0,
                        "call_count": 0
                    }
                    cls._instance._stats_lock = threading.Lock()
        return cls._instance
    
    def record(self, prompt_tokens: int, completion_tokens: int, total_tokens: int):
        """记录一次 API 调用的 token 使用情况"""
        with self._stats_lock:
            self.stats["total_prompt_tokens"] += prompt_tokens
            self.stats["total_completion_tokens"] += completion_tokens
            self.stats["total_tokens"] += total_tokens
            self.stats["call_count"] += 1
    
    def get_stats(self) -> Dict:
        """获取当前统计信息"""
        with self._stats_lock:
            return self.stats.copy()
    
    def reset(self):
        """重置统计信息"""
        with self._stats_lock:
            self.stats = {
                "total_prompt_tokens": 0,
                "total_completion_tokens": 0,
                "total_tokens": 0,
                "call_count": 0
            }


# 全局 token 追踪器实例
_token_tracker = TokenTracker()


def get_token_stats() -> Dict:
    """获取全局 token 使用统计信息"""
    return _token_tracker.get_stats()


def reset_token_stats():
    """重置全局 token 使用统计信息"""
    _token_tracker.reset()



# 抽象基类，定义了统一的接口
class BaseChatModel(ABC):
    def __init__(self, config: LLMConfig):
        self.config = config
        # 从文件加载system prompt
        import os
        system_prompt_path = os.path.join(os.path.dirname(__file__), 'prompts', 'system_prompt.txt')
        try:
            with open(system_prompt_path, 'r', encoding='utf-8') as f:
                system_prompt = f.read()
        except Exception as e:
            system_prompt = "You are a helpful assistant."
            print(f"Warning: Failed to load system prompt from {system_prompt_path}: {e}")
        self.messages = [{"role": "system", "content": system_prompt}]

    @abstractmethod
    def generate_response(self, user_input: str) -> str:
        """
        根据用户Input生成响应。
        子类必须实现此方法。
        """
        pass

    def _process_response_think_tags(self, response_text: str) -> str:
        """
        根据配置处理响应中的 <think> 标签。
        """
        if not self.config.think_mode_enabled:
            # 如果 think_mode_enabled 为 False，则移除 <think>...</think> 部分
            return re.sub(r'<think>.*?</think>', '', response_text, flags=re.DOTALL)
        return response_text


# 使用 OpenAI 兼容 API 的 LLM 类
class OpenAILLM(BaseChatModel):
    def __init__(self, config: LLMConfig):
        super().__init__(config)
        self.client = openai.OpenAI(
            base_url=self.config.base_url,
            api_key=self.config.api_key
        )
        # 为 OpenAI API 使用其特定的模型Name和温度
        self.model_name = self.config.api_model
        self.temperature = self.config.api_temperature
        self.top_p =self.config.api_top_p


    def generate_response(self, user_input: str) -> str:
        try:
            # 添加用户Input到消息历史
            self.messages.append({"role": "user", "content": user_input})

            # 调用 OpenAI API
            response = self.client.chat.completions.create(
                model=self.model_name,
                messages=self.messages,
                temperature=self.temperature,
                top_p = self.top_p
            )

            assistant_response = response.choices[0].message.content
            
            # 记录 token 使用情况
            if response.usage:
                _token_tracker.record(
                    prompt_tokens=response.usage.prompt_tokens,
                    completion_tokens=response.usage.completion_tokens,
                    total_tokens=response.usage.total_tokens
                )
            
            # 处理 <think> 标签，并更新历史
            processed_response = self._process_response_think_tags(assistant_response)
            self.messages.append({"role": "assistant", "content": assistant_response}) # 原始响应加入历史以保持完整上下文

            return processed_response

        except Exception as e:
            print(f"OpenAI API 调用失败: {e}")
            # 从历史中移除失败的用户Input，避免下次重复发送
            if self.messages and self.messages[-1]["role"] == "user":
                self.messages.pop()
            return f"生成响应失败: {e}"

# 本地 Transformers 模型（单 GPU，推理串行执行）
class LocalLLM(BaseChatModel):
    """
    使用 HuggingFace Transformers 加载本地模型。

    设计要点：
    - 支持同一路径多副本：local_model_replicas > 1 时并发占用显存。
    - 模型/tokenizer 以 local_model_instance_key 缓存；副本自动生成 replica key。
    - 同一副本串行推理（防 OOM），不同副本并行推理。
    - local_max_workers 控制线程池大小，决定同时"准备 prompt"的并发度，
      实际 GPU 计算并发度由“模型数 + 每模型锁”共同决定。
    """

    def __init__(self, config: LLMConfig):
        super().__init__(config)
        if not config.local_model_path:
            raise ValueError("local_model_path is empty; cannot initialize LocalLLM.")
        self._replicas: List[Tuple[Any, Any, threading.Lock]] = []
        self._rr_lock = threading.Lock()
        self._rr_counter = 0
        self._build_replicas()

    def _build_replicas(self) -> None:
        reps = max(1, int(self.config.local_model_replicas))
        paths = [self.config.local_model_path] * reps

        for idx, path in enumerate(paths):
            explicit_key = (self.config.local_model_instance_key or "").strip()
            if explicit_key and len(paths) == 1:
                instance_key = explicit_key
            else:
                instance_key = f"{path}::replica_{idx + 1}"
            model, tokenizer = self._get_or_load_model(path, instance_key)
            lock = _get_model_lock(instance_key)
            self._replicas.append((model, tokenizer, lock))

        if not self._replicas:
            raise RuntimeError("No local model replicas initialized.")

    def _acquire_replica(self) -> Tuple[Any, Any, threading.Lock]:
        n = len(self._replicas)
        with self._rr_lock:
            start = self._rr_counter % n
            self._rr_counter += 1

        # Prefer non-blocking acquisition for higher parallel utilization.
        for off in range(n):
            model, tokenizer, lock = self._replicas[(start + off) % n]
            if lock.acquire(blocking=False):
                return model, tokenizer, lock

        # If all busy, block on round-robin selected replica.
        model, tokenizer, lock = self._replicas[start]
        lock.acquire()
        return model, tokenizer, lock

    @staticmethod
    def _get_or_load_model(path: str, instance_key: str):
        """线程安全地加载或复用已缓存的模型。"""
        with _local_cache_lock:
            # 二次检查：防止等锁期间其他线程已完成加载
            if instance_key in _local_model_cache:
                return _local_model_cache[instance_key]
            try:
                import torch
                from transformers import AutoModelForCausalLM, AutoTokenizer
            except ImportError as e:
                raise ImportError(
                    "transformers and torch are required for local model inference. "
                    f"Install them with: pip install transformers torch\n{e}"
                )
            print(f"[LocalLLM] Loading model from {path} ...")
            tokenizer = AutoTokenizer.from_pretrained(path, trust_remote_code=True)
            model = AutoModelForCausalLM.from_pretrained(
                path,
                torch_dtype=torch.float16,
                device_map="auto",
                trust_remote_code=True,
            )
            model.eval()

            # Some chat models (e.g., Qwen) may not define pad_token.
            # Align pad token to eos token to keep generation stable.
            if tokenizer.pad_token_id is None:
                tokenizer.pad_token = tokenizer.eos_token
            model.config.pad_token_id = tokenizer.pad_token_id
            if hasattr(model, "generation_config") and model.generation_config is not None:
                model.generation_config.pad_token_id = tokenizer.pad_token_id

            _local_model_cache[instance_key] = (model, tokenizer)
            _local_model_locks.setdefault(instance_key, threading.Lock())
            print(f"[LocalLLM] Model loaded.")
            return _local_model_cache[instance_key]

    def generate_response(self, user_input: str) -> str:
        self.messages.append({"role": "user", "content": user_input})

        model, tokenizer, lock = self._acquire_replica()
        try:
            import torch
            # Build text first, then tokenize to get both input_ids and attention_mask.
            try:
                text = tokenizer.apply_chat_template(
                    self.messages,
                    tokenize=False,
                    add_generation_prompt=True,
                )
            except Exception:
                # 回退：简单拼接角色文本
                text = "\n".join(
                    f"{m['role']}: {m['content']}" for m in self.messages
                )

            max_len = getattr(self.config, "local_max_length", 4096)
            inputs = tokenizer(
                text,
                return_tensors="pt",
                truncation=True,
                max_length=max_len,
                padding=False,
            )
            inputs = {k: v.to(model.device) for k, v in inputs.items()}

            with torch.no_grad():
                output_ids = model.generate(
                    **inputs,
                    max_new_tokens=self.config.local_max_new_tokens,
                    temperature=self.config.local_temperature,
                    top_p=self.config.local_top_p,
                    do_sample=True,
                    pad_token_id=tokenizer.pad_token_id,
                )

            new_tokens = output_ids[0][inputs["input_ids"].shape[-1]:]
            raw_response = tokenizer.decode(new_tokens, skip_special_tokens=True)
        finally:
            lock.release()

        processed = self._process_response_think_tags(raw_response)
        self.messages.append({"role": "assistant", "content": raw_response})
        return processed


# 主控制类，根据配置选择使用哪种 LLM 实现
class Chatbot:
    def __init__(self, config: LLMConfig):
        self.config = config
        if config.use_api_model:
            self.llm_instance = OpenAILLM(config)
        elif config.local_model_path:
            self.llm_instance = LocalLLM(config)
        else:
            print("Warning: use_api_model is False and local_model_path is empty; "
                  "no LLM instance created.")
            self.llm_instance = None

    def chat(self, user_input: str) -> str:
        if self.llm_instance is None:
            print("Error: LLM instance is None, cannot generate response")
            return "Error: LLM instance not initialized"
        return self.llm_instance.generate_response(user_input)



# 示例用法
if __name__ == "__main__":
    # --- 示例 1: 使用 API 模型 ---
    print("--- 示例 1: 使用 API 模型 ---")
    api_config = LLMConfig()
    api_config.use_api_model = True 
    api_bot = Chatbot(api_config)

    user_input_api_1 = "你好，你是一个什么样的助手？"
    print(f"User: {user_input_api_1}")
    response_api_1 = api_bot.chat(user_input_api_1)
    print(f"Bot: {response_api_1}")
    print("----------------------")

    user_input_api_2 = "请问草莓(strawberries)里有多少个字母 'r'？"
    print(f"User: {user_input_api_2}")
    response_api_2 = api_bot.chat(user_input_api_2)
    print(f"Bot: {response_api_2}")
    print("----------------------")


 
