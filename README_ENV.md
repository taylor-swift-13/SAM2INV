# SAM2INV 环境配置

## 1) Python 环境

```bash
conda env create -f environment.yml
conda activate sam2inv
```

核心依赖：Python 3.10.12、vllm 0.8.0、torch。

## 2) Frama-C 29.0（OPAM）

```bash
sudo apt-get update
sudo apt-get install -y opam m4 pkg-config libgmp-dev z3

opam init --disable-sandboxing -y
eval "$(opam env)"
opam switch create sam2inv ocaml-base-compiler.4.14.2
eval "$(opam env --switch=sam2inv --set-switch)"

opam install -y frama-c.29.0
```

## 3) 日常激活

```bash
conda activate sam2inv
eval "$(opam env --switch=sam2inv --set-switch)"
```

## 4) 验证

```bash
python --version          # 3.10.12
frama-c -version          # 29.0
z3 --version

cd src
python3 loop_inv.py 1 --input-subdir NLA_lipus --max-iterations 1
```
