import openai
import re
import threading
from config import LLMConfig
from abc import ABC, abstractmethod
from typing import Dict, List, Optional, Tuple


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
        if not response_text:
            return ""
        if not self.config.think_mode_enabled:
            # 如果 think_mode_enabled 为 False，则移除 <think>...</think> 部分
            return re.sub(r'<think>.*?</think>', '', response_text, flags=re.DOTALL)
        return response_text


# 使用 OpenAI 兼容 API 的 LLM 类（云端模式）
class OpenAILLM(BaseChatModel):
    def __init__(self, config: LLMConfig):
        super().__init__(config)
        self.model_name = config.api_model
        self._clients = [openai.OpenAI(base_url=config.base_url, api_key=config.api_key)]
        self._rr_lock = threading.Lock()
        self._rr_counter = 0
        self.temperature = self.config.api_temperature
        self.top_p = self.config.api_top_p
        self.max_tokens = max(1, int(getattr(self.config, "api_max_tokens", 256)))

    def _next_client(self):
        with self._rr_lock:
            idx = self._rr_counter % len(self._clients)
            self._rr_counter += 1
        return self._clients[idx]

    def _coerce_message_content_to_text(self, content) -> str:
        """Normalize OpenAI message.content (string/list/None) into plain text."""
        if content is None:
            return ""
        if isinstance(content, str):
            return content
        if isinstance(content, list):
            parts: List[str] = []
            for item in content:
                if isinstance(item, str):
                    if item:
                        parts.append(item)
                    continue
                if isinstance(item, dict):
                    if item.get("type") == "text":
                        txt = item.get("text", "")
                        if isinstance(txt, str) and txt:
                            parts.append(txt)
                    continue
                item_type = getattr(item, "type", "")
                if item_type == "text":
                    txt = getattr(item, "text", "")
                    if isinstance(txt, str) and txt:
                        parts.append(txt)
            return "\n".join(parts).strip()
        return str(content)

    def generate_response(self, user_input: str) -> str:
        try:
            # 添加用户Input到消息历史
            self.messages.append({"role": "user", "content": user_input})

            def _call_chat(max_tokens: int):
                return self._next_client().chat.completions.create(
                    model=self.model_name,
                    messages=self.messages,
                    temperature=self.temperature,
                    top_p=self.top_p,
                    max_tokens=max_tokens
                )

            # 调用 OpenAI API（并在“空内容+length”时自动重试一次）
            response = _call_chat(self.max_tokens)
            choice = response.choices[0]
            msg = choice.message

            raw_content = msg.content
            assistant_response = self._coerce_message_content_to_text(raw_content)
            if not assistant_response:
                fallback_refusal = getattr(msg, "refusal", None)
                if isinstance(fallback_refusal, str) and fallback_refusal.strip():
                    assistant_response = fallback_refusal.strip()
            if (
                not assistant_response
                and getattr(choice, "finish_reason", None) == "length"
                and self.max_tokens < 8192
            ):
                retry_max_tokens = min(8192, max(self.max_tokens * 4, 1024))
                response = _call_chat(retry_max_tokens)
                choice = response.choices[0]
                msg = choice.message
                raw_content = msg.content
                assistant_response = self._coerce_message_content_to_text(raw_content)
                if not assistant_response:
                    fallback_refusal = getattr(msg, "refusal", None)
                    if isinstance(fallback_refusal, str) and fallback_refusal.strip():
                        assistant_response = fallback_refusal.strip()
            
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

# ==============================================================================
# vLLM 本地推理（in-process，无 HTTP 服务层）
# ==============================================================================

# 进程级单例：避免重复加载大模型
_vllm_instance: Optional["VLLMClient"] = None
_vllm_lock = threading.Lock()


class VLLMClient:
    """
    封装 vLLM 推理引擎。进程内单例，模型只加载一次。
    gpu_count  : tensor parallel GPU 数
    gpu_mem    : 每张 GPU 显存利用率 (0~1)
    """

    def __init__(self, model_path: str, gpu_count: int = 1, gpu_mem: float = 0.90):
        from vllm import LLM, SamplingParams  # 延迟导入，仅 use_local=True 时才需要 vllm

        print(f"[VLLMClient] 正在初始化 vLLM 引擎 [model={model_path}, GPUs={gpu_count}] ...")
        self._SamplingParams = SamplingParams
        self.llm = LLM(
            model=model_path,
            tensor_parallel_size=gpu_count,
            gpu_memory_utilization=gpu_mem,
            trust_remote_code=True,
            max_model_len=8192,
            enable_prefix_caching=True,
        )
        self.default_sampling_params = SamplingParams(
            temperature=1.0,
            top_p=1.0,
            max_tokens=8192,
        )
        print("[VLLMClient] 模型加载完毕。")

    def chat_messages(
        self,
        messages: List[Dict],
        sampling_params=None,
    ) -> Tuple[str, int, int]:
        """
        以 OpenAI messages 格式调用 vLLM（自动应用 chat template）。
        返回 (生成文本, prompt_tokens, completion_tokens)。
        """
        params = sampling_params if sampling_params else self.default_sampling_params
        outputs = self.llm.chat(messages, params)
        out = outputs[0]
        text = out.outputs[0].text.strip()
        prompt_tokens = len(out.prompt_token_ids)
        completion_tokens = len(out.outputs[0].token_ids)
        return text, prompt_tokens, completion_tokens

    def chat(self, prompt: str, sampling_params=None) -> str:
        """
        单轮推理：接受完整的字符串 prompt，返回生成文本。
        """
        params = sampling_params if sampling_params else self.default_sampling_params
        outputs = self.llm.generate([prompt], params)
        return outputs[0].outputs[0].text.strip()


def _get_vllm_client(config: LLMConfig) -> VLLMClient:
    """返回进程级 VLLMClient 单例（首次调用时初始化）。"""
    global _vllm_instance
    with _vllm_lock:
        if _vllm_instance is None:
            _vllm_instance = VLLMClient(
                model_path=config.vllm_model_path,
                gpu_count=config.vllm_gpu_count,
                gpu_mem=config.vllm_gpu_mem,
            )
    return _vllm_instance


class VLLMLLMImpl(BaseChatModel):
    """使用进程内 vLLM 引擎的 LLM 实现，接口与 OpenAILLM 完全一致。"""

    def __init__(self, config: LLMConfig):
        super().__init__(config)
        self._client = _get_vllm_client(config)
        from vllm import SamplingParams
        self._sampling_params = SamplingParams(
            temperature=max(0.0, float(config.api_temperature)),
            top_p=max(0.0, min(1.0, float(config.api_top_p))),
            max_tokens=max(1, int(config.api_max_tokens)),
        )

    def generate_response(self, user_input: str) -> str:
        self.messages.append({"role": "user", "content": user_input})
        try:
            text, prompt_tokens, completion_tokens = self._client.chat_messages(
                self.messages,
                sampling_params=self._sampling_params,
            )
            _token_tracker.record(
                prompt_tokens=prompt_tokens,
                completion_tokens=completion_tokens,
                total_tokens=prompt_tokens + completion_tokens,
            )
            processed = self._process_response_think_tags(text)
            # 原始响应存入历史以保持完整上下文
            self.messages.append({"role": "assistant", "content": text})
            return processed
        except Exception as e:
            print(f"vLLM 推理失败: {e}")
            if self.messages and self.messages[-1]["role"] == "user":
                self.messages.pop()
            return f"生成响应失败: {e}"


# ==============================================================================
# Transformers 本地推理（单卡 / CPU，无需安装 vllm）
# ==============================================================================

_hf_instance: Optional["TransformersClient"] = None
_hf_lock = threading.Lock()


class TransformersClient:
    """
    封装 HuggingFace Transformers 推理。进程内单例，模型只加载一次。
    适合单卡或 CPU 场景，不依赖 vllm。
    """

    def __init__(self, model_path: str):
        import torch
        from transformers import AutoModelForCausalLM, AutoTokenizer

        print(f"[TransformersClient] 正在加载模型: {model_path} ...")
        self.tokenizer = AutoTokenizer.from_pretrained(model_path, trust_remote_code=True)
        self.model = AutoModelForCausalLM.from_pretrained(
            model_path,
            torch_dtype=torch.float16 if torch.cuda.is_available() else torch.float32,
            device_map="auto",
            trust_remote_code=True,
        )
        self.model.eval()
        if self.tokenizer.pad_token_id is None:
            self.tokenizer.pad_token = self.tokenizer.eos_token
        self.model.config.pad_token_id = self.tokenizer.pad_token_id
        print("[TransformersClient] 模型加载完毕。")

    def chat_messages(
        self,
        messages: List[Dict],
        temperature: float = 1.0,
        top_p: float = 1.0,
        max_new_tokens: int = 8192,
    ) -> Tuple[str, int, int]:
        """
        以 OpenAI messages 格式调用，返回 (生成文本, prompt_tokens, completion_tokens)。
        """
        import torch

        try:
            prompt_text = self.tokenizer.apply_chat_template(
                messages, tokenize=False, add_generation_prompt=True
            )
        except Exception:
            prompt_text = "\n".join(f"{m['role']}: {m['content']}" for m in messages)

        inputs = self.tokenizer(
            prompt_text,
            return_tensors="pt",
            truncation=True,
            max_length=8192,
            padding=False,
        )
        inputs = {k: v.to(self.model.device) for k, v in inputs.items()}
        prompt_tokens = int(inputs["input_ids"].shape[-1])

        with torch.no_grad():
            output_ids = self.model.generate(
                **inputs,
                max_new_tokens=max(1, max_new_tokens),
                temperature=max(0.0, float(temperature)),
                top_p=max(0.0, min(1.0, float(top_p))),
                do_sample=float(temperature) > 0.0,
                pad_token_id=self.tokenizer.pad_token_id,
            )

        new_tokens = output_ids[0][prompt_tokens:]
        text = self.tokenizer.decode(new_tokens, skip_special_tokens=True).strip()
        completion_tokens = int(new_tokens.shape[-1])
        return text, prompt_tokens, completion_tokens


def _get_hf_client(config: LLMConfig) -> TransformersClient:
    """返回进程级 TransformersClient 单例。"""
    global _hf_instance
    with _hf_lock:
        if _hf_instance is None:
            _hf_instance = TransformersClient(model_path=config.vllm_model_path)
    return _hf_instance


class TransformersLLMImpl(BaseChatModel):
    """使用 HuggingFace Transformers 的本地 LLM 实现，接口与其他实现完全一致。"""

    def __init__(self, config: LLMConfig):
        super().__init__(config)
        self._client = _get_hf_client(config)
        self._temperature = float(config.api_temperature)
        self._top_p = float(config.api_top_p)
        self._max_tokens = max(1, int(config.api_max_tokens))

    def generate_response(self, user_input: str) -> str:
        self.messages.append({"role": "user", "content": user_input})
        try:
            text, prompt_tokens, completion_tokens = self._client.chat_messages(
                self.messages,
                temperature=self._temperature,
                top_p=self._top_p,
                max_new_tokens=self._max_tokens,
            )
            _token_tracker.record(
                prompt_tokens=prompt_tokens,
                completion_tokens=completion_tokens,
                total_tokens=prompt_tokens + completion_tokens,
            )
            processed = self._process_response_think_tags(text)
            self.messages.append({"role": "assistant", "content": text})
            return processed
        except Exception as e:
            print(f"Transformers 推理失败: {e}")
            if self.messages and self.messages[-1]["role"] == "user":
                self.messages.pop()
            return f"生成响应失败: {e}"


# ==============================================================================
# 主控制类：根据配置自动选择后端
#   use_local=False              → OpenAILLM   (云端 API)
#   use_local=True, use_vllm=True  → VLLMLLMImpl  (vLLM 高吞吐)
#   use_local=True, use_vllm=False → TransformersLLMImpl (HF Transformers)
# ==============================================================================
class Chatbot:
    def __init__(self, config: LLMConfig):
        self.config = config
        if getattr(config, "use_local", False):
            if getattr(config, "use_vllm", True):
                self.llm_instance = VLLMLLMImpl(config)
            else:
                self.llm_instance = TransformersLLMImpl(config)
        else:
            self.llm_instance = OpenAILLM(config)

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


 
