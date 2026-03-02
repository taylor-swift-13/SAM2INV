#!/usr/bin/env python3
"""
vLLM 独立推理脚本（原 local_openai_service.py 已废弃）。

之前的做法：用 FastAPI + Transformers 启动 HTTP 服务，再用 OpenAI 客户端访问。
现在的做法：直接在进程内通过 vllm.LLM 推理，无需任何 HTTP 服务层。

此脚本作为 VLLMClient 的独立使用示例，可单独运行验证环境。
"""
from __future__ import annotations

import argparse
import sys
from pathlib import Path

# 将 src/ 加入路径，使 VLLMClient 可直接导入
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

from llm import VLLMClient  # type: ignore
from vllm import SamplingParams  # type: ignore


def main() -> None:
    parser = argparse.ArgumentParser(description="vLLM 独立推理示例")
    parser.add_argument("--model-path", required=True, help="本地模型路径（HuggingFace 格式）")
    parser.add_argument("--gpu-count", type=int, default=1, help="Tensor parallel GPU 数量")
    parser.add_argument("--gpu-mem", type=float, default=0.90, help="GPU 显存利用率 (0~1)")
    parser.add_argument("--prompt", type=str, default="你好，请介绍一下你自己。", help="测试 prompt")
    parser.add_argument("--max-tokens", type=int, default=512, help="最大生成 token 数")
    parser.add_argument("--temperature", type=float, default=0.0, help="采样温度")
    args = parser.parse_args()

    # 初始化（全局仅此一次）
    client = VLLMClient(
        model_path=args.model_path,
        gpu_count=args.gpu_count,
        gpu_mem=args.gpu_mem,
    )

    sampling_params = SamplingParams(
        temperature=args.temperature,
        max_tokens=args.max_tokens,
    )

    # 单轮推理示例
    print(f"\n[Prompt] {args.prompt}")
    response = client.chat(args.prompt, sampling_params=sampling_params)
    print(f"[Response] {response}")

    # 多轮对话示例（messages 格式）
    messages = [
        {"role": "system", "content": "你是一个有帮助的助手。"},
        {"role": "user", "content": args.prompt},
    ]
    text, pt, ct = client.chat_messages(messages, sampling_params=sampling_params)
    print(f"\n[Messages] prompt_tokens={pt}  completion_tokens={ct}")
    print(f"[Response] {text}")


if __name__ == "__main__":
    main()
