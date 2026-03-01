#!/usr/bin/env python3
from __future__ import annotations

import argparse
import time
from typing import Any, Dict, List, Optional

import torch
from fastapi import FastAPI, HTTPException
from pydantic import BaseModel
from transformers import AutoModelForCausalLM, AutoTokenizer
import uvicorn


class ChatMessage(BaseModel):
    role: str
    content: str


class ChatCompletionRequest(BaseModel):
    model: str
    messages: List[ChatMessage]
    temperature: float = 1.0
    top_p: float = 1.0
    max_tokens: int = 1024


def build_app(
    model_path: str,
    served_model_name: str,
    api_key: str,
    max_model_len: int,
) -> FastAPI:
    app = FastAPI()

    print(f"[local-api] Loading model from {model_path} ...")
    tokenizer = AutoTokenizer.from_pretrained(model_path, trust_remote_code=True)
    model = AutoModelForCausalLM.from_pretrained(
        model_path,
        torch_dtype=torch.float16 if torch.cuda.is_available() else torch.float32,
        device_map="auto",
        trust_remote_code=True,
    )
    model.eval()

    if tokenizer.pad_token_id is None:
        tokenizer.pad_token = tokenizer.eos_token
    model.config.pad_token_id = tokenizer.pad_token_id
    if getattr(model, "generation_config", None) is not None:
        model.generation_config.pad_token_id = tokenizer.pad_token_id
    print("[local-api] Model loaded.")

    def _auth_ok(auth_header: Optional[str]) -> bool:
        if not api_key:
            return True
        if not auth_header:
            return False
        return auth_header.strip() == f"Bearer {api_key}"

    @app.get("/v1/models")
    def list_models(authorization: Optional[str] = None) -> Dict[str, Any]:
        if not _auth_ok(authorization):
            raise HTTPException(status_code=401, detail="Unauthorized")
        return {"object": "list", "data": [{"id": served_model_name, "object": "model"}]}

    @app.post("/v1/chat/completions")
    def chat_completions(req: ChatCompletionRequest, authorization: Optional[str] = None) -> Dict[str, Any]:
        if not _auth_ok(authorization):
            raise HTTPException(status_code=401, detail="Unauthorized")
        if req.model != served_model_name:
            raise HTTPException(status_code=400, detail=f"Unknown model: {req.model}")

        msgs = [{"role": m.role, "content": m.content} for m in req.messages]
        try:
            text = tokenizer.apply_chat_template(
                msgs,
                tokenize=False,
                add_generation_prompt=True,
            )
        except Exception:
            text = "\n".join(f"{m['role']}: {m['content']}" for m in msgs)

        inputs = tokenizer(
            text,
            return_tensors="pt",
            truncation=True,
            max_length=max_model_len,
            padding=False,
        )
        inputs = {k: v.to(model.device) for k, v in inputs.items()}

        with torch.no_grad():
            output_ids = model.generate(
                **inputs,
                max_new_tokens=max(1, int(req.max_tokens)),
                temperature=max(0.0, float(req.temperature)),
                top_p=max(0.0, min(1.0, float(req.top_p))),
                do_sample=float(req.temperature) > 0.0,
                pad_token_id=tokenizer.pad_token_id,
            )

        new_tokens = output_ids[0][inputs["input_ids"].shape[-1] :]
        content = tokenizer.decode(new_tokens, skip_special_tokens=True)
        prompt_tokens = int(inputs["input_ids"].shape[-1])
        completion_tokens = int(new_tokens.shape[-1])
        total_tokens = prompt_tokens + completion_tokens
        now = int(time.time())

        return {
            "id": f"chatcmpl-{now}",
            "object": "chat.completion",
            "created": now,
            "model": served_model_name,
            "choices": [
                {
                    "index": 0,
                    "message": {"role": "assistant", "content": content},
                    "finish_reason": "stop",
                }
            ],
            "usage": {
                "prompt_tokens": prompt_tokens,
                "completion_tokens": completion_tokens,
                "total_tokens": total_tokens,
            },
        }

    return app


def main() -> None:
    parser = argparse.ArgumentParser(description="OpenAI-compatible local chat service (Transformers backend).")
    parser.add_argument("--model-path", required=True, help="Local model path.")
    parser.add_argument("--served-model-name", default="qwen-local", help="Model id exposed at /v1.")
    parser.add_argument("--host", default="0.0.0.0")
    parser.add_argument("--port", type=int, default=8000)
    parser.add_argument("--api-key", default="EMPTY", help="Bearer token required by API clients.")
    parser.add_argument("--max-model-len", type=int, default=8192)
    args = parser.parse_args()

    app = build_app(
        model_path=args.model_path,
        served_model_name=args.served_model_name,
        api_key=args.api_key,
        max_model_len=args.max_model_len,
    )
    uvicorn.run(app, host=args.host, port=args.port, log_level="info")


if __name__ == "__main__":
    main()
