# SAM2INV

SAM2INV (Sample to Invariant) generates ACSL loop invariants for C programs and verifies them with Frama-C/WP.

## Repository Structure

```text
SAM2INV/
├── README.md
├── README_ENV.md
├── environment.yml
├── sam2inv.opam
├── opam-packages.txt
├── src/
│   ├── loop_inv.py                # Main entry point for one C file
│   ├── run_all_tests.py           # Batch runner for one input subdirectory
│   ├── config.py                  # Runtime configuration
│   ├── input/                     # Input C files grouped by subdirectory
│   ├── output/                    # Generated annotated C files
│   ├── log/                       # Logs
│   └── scripts/
│       ├── opam.sh                # opam environment activation helper
│       └── start_local_services_from_config.py
├── loop_factory/                  # Loop/program generation pipelines
└── VST/                           # Related proof artifacts
```

## Requirements

- Python 3.11 (recommended; see `environment.yml`)
- Frama-C available in `PATH`
- Z3 available in `PATH`
- `opam` (recommended for Frama-C/OCaml toolchain management)

## Environment Setup

Use the dedicated setup guide:

- [README_ENV.md](README_ENV.md)

Environment-related files:

- Conda: `environment.yml`
- OPAM package: `sam2inv.opam`
- OPAM fallback list: `opam-packages.txt`
- OPAM activation script: `src/scripts/opam.sh`

Validation modes (details in `README_ENV.md`):

- Full validation: create temp env directly from `environment.yml`
- Lightweight validation: verify core Python deps when heavy packages are unstable under proxy/network

## Configuration

Main runtime configuration is in `src/config.py`.

Common fields:

- `LLMConfig.api_model`
- `LLMConfig.api_key`
- `LLMConfig.base_url`
- `LLMConfig.api_base_urls`
- `SUBDIR`
- `MAX_ITERATION`
- `MAX_STRENGTHEN_ITERATIONS`
- `PARALLEL_GENERATION_CONFIG`
- `LOOP_FACTORY_USER_CONFIG`
- `LOCAL_MODEL_SERVICE_CONFIG`

Notes:

- Avoid hardcoding API keys in committed files.
- API 配置支持环境变量覆盖：`OPENAI_BASE_URL`、`OPENAI_MODEL`、`OPENAI_API_KEY`。

## Run Local Model As API Service (Recommended)

建议将本地模型作为 OpenAI 兼容服务启动，SAM2INV 只走 API 调用。

### 1. 配置本地模型路径与实例数（仅两个参数）

在 `src/config.py` 中设置：

```python
LOCAL_MODEL_SERVICE_CONFIG = {
    'model_path': '/path/to/Qwen-Model',
    'num_instances': 6,
}
```

### 2. 一键启动本地服务（Transformers 后端）

```bash
cd src
python3 scripts/start_local_services_from_config.py
```

脚本会输出一行逗号分隔 URL（`OPENAI_BASE_URLS` 值）。

依赖（按需安装）：

```bash
pip install fastapi uvicorn transformers torch
```

### 3. SAM2INV 使用 API 调用本地服务

```bash
export OPENAI_BASE_URLS=http://127.0.0.1:8001/v1,http://127.0.0.1:8002/v1
export OPENAI_MODEL=qwen-local
export OPENAI_API_KEY=EMPTY
```

如果只启了一个实例，也可以只设 `OPENAI_BASE_URL`。

## Run One File

From `src`:

```bash
cd src
python3 loop_inv.py <file_name> [--input-subdir SUBDIR] [--max-iterations N]
```

Example:

```bash
python3 loop_inv.py 1 --input-subdir NLA_lipus --max-iterations 1
```

Output locations:

- Annotated C: `src/output/<subdir>/`
- Logs: `src/log/<subdir>/`

## Run a Test Set

From `src`:

```bash
python3 run_all_tests.py <test_set> [--workers N] [--max-iterations N]
```

Example:

```bash
python3 run_all_tests.py NLA_lipus --workers 20 --max-iterations 1
```

## Troubleshooting

1. `frama-c: command not found`
- Activate opam first: `eval "$(opam env)"` or `source src/scripts/opam.sh sam2inv`

2. `z3` not found by Frama-C/WP
- Check `which z3`
- Reinstall system `z3` if needed

3. Python import errors
- Ensure conda env `sam2inv` is activated
- Recreate env if needed: `conda env remove -n sam2inv -y && conda env create -f environment.yml`

## Minimal Health Check

```bash
cd /path/to/SAM2INV
conda activate sam2inv
source src/scripts/opam.sh sam2inv

frama-c -version
why3 --version
alt-ergo --version
z3 --version

cd src
python3 loop_inv.py 1 --input-subdir NLA_lipus --max-iterations 1
```
