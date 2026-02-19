# SAM2INV

SAM2INV (Sample to Invariant) automatically generates ACSL loop invariants for C programs and verifies them with Frama-C/WP.

## 1. Repository Layout

```text
SAM2INV/
├── README.md
├── src/
│   ├── loop_inv.py          # Main entry point
│   ├── config.py            # Runtime configuration (model, sampling, parallelism)
│   ├── input/               # Input C files
│   ├── output/              # Generated outputs
│   └── log/                 # Logs
├── loop_factory/            # Data/loop generation tools
└── VST/                     # Related verification artifacts
```

## 2. Requirements

- Python 3.8+
- Frama-C (required, `frama-c` must be available in PATH)
- Z3 (used by Frama-C/WP)
- `opam` is strongly recommended to manage Frama-C and OCaml dependencies

## 3. Python Environment Setup

Run in the repository root:

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install --upgrade pip
pip install z3-solver numpy chromadb sentence-transformers openai pyyaml
```

Note: this repository currently does not provide a dedicated `requirements.txt`.

## 4. OPAM/Frama-C Setup (Important)

### 4.1 Install opam (Ubuntu/Debian)

```bash
sudo apt-get update
sudo apt-get install -y opam m4 bubblewrap pkg-config libgmp-dev
```

### 4.2 Initialize opam

```bash
opam init --disable-sandboxing -y
```

Then load opam environment in your current shell:

```bash
eval "$(opam env)"
```

### 4.3 Create and activate a dedicated switch (recommended)

```bash
opam switch create sam2inv ocaml-base-compiler.4.14.1 -y
opam switch sam2inv
eval "$(opam env --switch=sam2inv --set-switch)"
```

### 4.4 Install Frama-C and provers

```bash
opam install -y frama-c why3 alt-ergo
```

Install Z3 system-wide (pick one):

```bash
# Ubuntu/Debian
sudo apt-get install -y z3

# macOS
brew install z3
```

### 4.5 Verify installation

```bash
which frama-c
frama-c -version
which z3
z3 --version
```

If all commands return valid paths/versions, your verification environment is ready.

## 5. What to Run in Every New Terminal

If Frama-C was installed in an opam switch, always activate it first:

```bash
eval "$(opam env --switch=sam2inv --set-switch)"
```

Then activate Python virtual environment:

```bash
source /path/to/SAM2INV/.venv/bin/activate
```

Optional (`~/.bashrc`):

```bash
echo 'eval "$(opam env --switch=sam2inv --set-switch)"' >> ~/.bashrc
```

## 6. Configure Model and Runtime Parameters

Edit `src/config.py`.

Most frequently changed fields:

- `LLMConfig.api_model`
- `LLMConfig.api_key`
- `LLMConfig.base_url`
- `SUBDIR` (default input subdirectory)
- `PARALLEL_GENERATION_CONFIG`

Recommendation: read API keys from environment variables instead of hardcoding.

## 7. Run

From `src`:

```bash
cd src
python3 loop_inv.py <file_name> [--input-subdir SUBDIR] [--max-iterations N]
```

Example:

```bash
python3 loop_inv.py 1 --input-subdir NLA_lipus
```

Outputs:

- Result file: `src/output/<subdir>/`
- Log file: `src/log/<subdir>/`

## 8. Common Issues

1. `frama-c: command not found`
- Usually caused by missing opam environment activation.
- Run: `eval "$(opam env --switch=sam2inv --set-switch)"`

2. WP prover errors
- Check `z3 --version`
- Ensure `which z3` returns a valid binary

3. Missing Python modules
- Ensure `.venv` is activated
- Re-run the `pip install` commands in Section 3

## 9. Minimal Health Check

```bash
# 1) opam environment
opam switch sam2inv
eval "$(opam env --switch=sam2inv --set-switch)"
frama-c -version

# 2) Python environment
cd /path/to/SAM2INV
source .venv/bin/activate

# 3) Run one sample
cd src
python3 loop_inv.py 1 --input-subdir NLA_lipus
```

If step 3 generates log/output files, the setup is working.
