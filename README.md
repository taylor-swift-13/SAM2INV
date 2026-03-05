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
│   └── scripts/opam.sh            # opam environment activation helper
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

After environment setup, activate before running:

```bash
conda activate sam2inv
source src/scripts/opam.sh sam2inv
```

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
