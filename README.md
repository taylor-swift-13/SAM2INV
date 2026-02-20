# SAM2INV

SAM2INV (Sample to Invariant) generates ACSL loop invariants for C programs and verifies them with Frama-C/WP.

## Repository Structure

```text
SAM2INV/
├── README.md
├── src/
│   ├── loop_inv.py                # Main entry point for one C file
│   ├── run_all_tests.py           # Batch runner for one input subdirectory
│   ├── config.py                  # Runtime configuration
│   ├── input/                     # Input C files grouped by subdirectory
│   ├── output/                    # Generated annotated C files
│   ├── log/                       # Logs
│   └── scripts/opam.sh            # `eval "$(opam env)"`
├── loop_factory/                  # Loop/program generation pipelines
└── VST/                           # Related proof artifacts
```

## Requirements

- Python 3.9+
- Frama-C available in `PATH`
- Z3 available in `PATH`
- `opam` (recommended for Frama-C/OCaml toolchain management)

## Environment Setup

### 1. Python Environment

From repository root:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install z3-solver numpy openai pyyaml
```

If your local workflow needs extra packages (for optional scripts), install them separately.

### 2. OPAM / Frama-C Environment

Install opam and system dependencies (Ubuntu/Debian example):

```bash
sudo apt-get update
sudo apt-get install -y opam m4 bubblewrap pkg-config libgmp-dev z3
```

Initialize opam:

```bash
opam init --disable-sandboxing -y
```

Activate opam in the current shell:

```bash
eval "$(opam env)"
```

Install Frama-C and provers:

```bash
opam install -y frama-c why3 alt-ergo
```

Quick check:

```bash
which frama-c && frama-c -version
which z3 && z3 --version
```

### 3. Shell Activation Shortcut

This repository provides:

```bash
source src/scripts/opam.sh
```

`src/scripts/opam.sh` only runs:

```bash
eval "$(opam env)"
```

## Configuration

Main runtime configuration is in `src/config.py`.

Common fields:

- `LLMConfig.api_model`
- `LLMConfig.api_key`
- `LLMConfig.base_url`
- `SUBDIR`
- `MAX_ITERATION`
- `MAX_STRENGTHEN_ITERATIONS`
- `PARALLEL_GENERATION_CONFIG`
- `LOOP_FACTORY_USER_CONFIG`

Notes:

- Cache-related logic has been removed from the current pipeline.
- Avoid hardcoding API keys in committed files.

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
- Activate opam first: `eval "$(opam env)"` or `source src/scripts/opam.sh`

2. `z3` not found by Frama-C/WP
- Check `which z3`
- Reinstall system `z3` if needed

3. Python import errors
- Ensure `.venv` is activated
- Reinstall required Python packages

## Minimal Health Check

```bash
cd /path/to/SAM2INV
source .venv/bin/activate
source src/scripts/opam.sh

frama-c -version
z3 --version

cd src
python3 loop_inv.py 1 --input-subdir NLA_lipus --max-iterations 1
```
