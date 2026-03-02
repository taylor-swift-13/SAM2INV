#!/usr/bin/env python3
"""
vLLM 引擎预热脚本（原 start_local_services_from_config.py 已废弃）。

之前的做法：从 LOCAL_MODEL_SERVICE_CONFIG 读取参数，启动多个 FastAPI+Transformers HTTP 进程。
现在的做法：vLLM 引擎直接在推理进程内加载（见 src/llm.py VLLMClient），无需独立服务进程。

此脚本读取 VLLM_ENGINE_CONFIG，提前触发 VLLMClient 单例初始化，用于预热验证。
"""
from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

import config as cfg_mod  # type: ignore
from config import LLMConfig  # type: ignore
from llm import _get_vllm_client  # type: ignore


def main() -> None:
    engine_cfg = getattr(cfg_mod, "VLLM_ENGINE_CONFIG", {})
    model_path = str(engine_cfg.get("model_path", "")).strip()
    if not model_path:
        raise RuntimeError("VLLM_ENGINE_CONFIG['model_path'] 未设置。")

    llm_cfg = LLMConfig(
        use_local=True,
        vllm_model_path=model_path,
        vllm_gpu_count=int(engine_cfg.get("gpu_count", 1)),
        vllm_gpu_mem=float(engine_cfg.get("gpu_mem", 0.90)),
    )

    print(f"[vllm-warmup] 预热 vLLM 引擎: {model_path}")
    client = _get_vllm_client(llm_cfg)
    # 发送一条空推理触发 KV-cache 及 CUDA 核编译
    client.chat("warm up", sampling_params=client._SamplingParams(temperature=0, max_tokens=1))
    print("[vllm-warmup] 引擎已就绪。")


if __name__ == "__main__":
    main()
