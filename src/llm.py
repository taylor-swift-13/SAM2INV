import openai
import re
import threading
from config import LLMConfig
from abc import ABC, abstractmethod
from typing import Dict, List


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


# 使用 OpenAI 兼容 API 的 LLM 类
class OpenAILLM(BaseChatModel):
    def __init__(self, config: LLMConfig):
        super().__init__(config)
        if getattr(config, "use_local", False):
            # 本地模式：支持多实例轮询
            urls = [u.strip() for u in config.local_base_urls.split(",") if u.strip()]
            if not urls:
                urls = ["http://127.0.0.1:8001/v1"]
            key = config.local_api_key or "EMPTY"
            self.model_name = config.local_model or ""
            self._clients = [openai.OpenAI(base_url=url, api_key=key) for url in urls]
        else:
            # 云端服务商模式
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

# 主控制类，根据配置选择使用哪种 LLM 实现
class Chatbot:
    def __init__(self, config: LLMConfig):
        self.config = config
        # Service-only architecture: always use OpenAI-compatible API.
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


 
