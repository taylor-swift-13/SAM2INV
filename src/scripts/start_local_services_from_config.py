#!/usr/bin/env python3
from __future__ import annotations

import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, List


def _load_cfg() -> Dict[str, object]:
    root = Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    import config  # type: ignore

    cfg = getattr(config, "LOCAL_MODEL_SERVICE_CONFIG", {})
    if not isinstance(cfg, dict):
        raise RuntimeError("LOCAL_MODEL_SERVICE_CONFIG is missing or not a dict")
    return cfg


def main() -> None:
    cfg = _load_cfg()
    root = Path(__file__).resolve().parents[1]
    script = root / "scripts" / "local_openai_service.py"
    log_dir = root / "log" / "local_api_instances"
    log_dir.mkdir(parents=True, exist_ok=True)

    model_path = str(cfg.get("model_path", "")).strip()
    if not model_path:
        raise RuntimeError("LOCAL_MODEL_SERVICE_CONFIG['model_path'] is empty.")

    n = max(1, int(cfg.get("num_instances", 1)))
    # Fixed defaults to keep configuration minimal.
    start_port = 8001
    served_model = "qwen-local"
    api_key = os.getenv("OPENAI_API_KEY", "EMPTY")
    max_model_len = 8192
    host = "0.0.0.0"

    urls: List[str] = []
    for i in range(n):
        port = start_port + i
        env = os.environ.copy()

        log_file = log_dir / f"instance_{port}.log"
        pid_file = log_dir / f"instance_{port}.pid"
        cmd = [
            sys.executable,
            str(script),
            "--model-path",
            model_path,
            "--served-model-name",
            served_model,
            "--host",
            host,
            "--port",
            str(port),
            "--api-key",
            api_key,
            "--max-model-len",
            str(max_model_len),
        ]
        with log_file.open("a", encoding="utf-8") as lf:
            proc = subprocess.Popen(
                cmd,
                cwd=str(root),
                env=env,
                stdout=lf,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        pid_file.write_text(str(proc.pid), encoding="utf-8")
        urls.append(f"http://127.0.0.1:{port}/v1")
        print(f"[started] port={port} pid={proc.pid} log={log_file}")

    joined = ",".join(urls)
    print(joined)


if __name__ == "__main__":
    main()
