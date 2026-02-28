import openai
import re
import threading
from config import LLMConfig
from abc import ABC, abstractmethod
from typing import Dict, List, Tuple, Any, Optional

# 本地模型推理锁：GPU 同一时刻只能跑一个推理，防止 OOM
_local_inference_lock = threading.Lock()
# 模型缓存：path -> (model, tokenizer)，避免多线程重复加载
_local_model_cache: Dict[str, Any] = {}

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
    - 模型/tokenizer 以 local_model_path 为 key 缓存在模块级 _local_model_cache 中，
      多个 LocalLLM 实例（来自不同线程）共享同一份权重，不会重复占用显存。
    - 所有推理调用通过 _local_inference_lock 串行化，GPU 同一时刻只执行一个前向传播。
    - local_max_workers 控制线程池大小，决定同时"准备 prompt"的并发度，
      但实际 GPU 计算始终是串行的。
    """

    def __init__(self, config: LLMConfig):
        super().__init__(config)
        if not config.local_model_path:
            raise ValueError("local_model_path is empty; cannot initialize LocalLLM.")
        self._model, self._tokenizer = self._get_or_load_model(config.local_model_path)

    @staticmethod
    def _get_or_load_model(path: str):
        """线程安全地加载或复用已缓存的模型。"""
        if path in _local_model_cache:
            return _local_model_cache[path]
        with _local_inference_lock:
            # 二次检查：防止等锁期间其他线程已完成加载
            if path in _local_model_cache:
                return _local_model_cache[path]
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
            _local_model_cache[path] = (model, tokenizer)
            print(f"[LocalLLM] Model loaded.")
            return _local_model_cache[path]

    def generate_response(self, user_input: str) -> str:
        self.messages.append({"role": "user", "content": user_input})

        with _local_inference_lock:
            import torch
            # 优先使用 apply_chat_template（支持 ChatML / Llama3 等格式）
            try:
                input_ids = self._tokenizer.apply_chat_template(
                    self.messages,
                    add_generation_prompt=True,
                    return_tensors="pt",
                ).to(self._model.device)
            except Exception:
                # 回退：简单拼接角色文本
                prompt = "\n".join(
                    f"{m['role']}: {m['content']}" for m in self.messages
                )
                input_ids = self._tokenizer(
                    prompt, return_tensors="pt"
                ).input_ids.to(self._model.device)

            with torch.no_grad():
                output_ids = self._model.generate(
                    input_ids,
                    max_new_tokens=self.config.local_max_new_tokens,
                    temperature=self.config.local_temperature,
                    top_p=self.config.local_top_p,
                    do_sample=True,
                )

            new_tokens = output_ids[0][input_ids.shape[-1]:]
            raw_response = self._tokenizer.decode(new_tokens, skip_special_tokens=True)

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


 
