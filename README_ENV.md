# SAM2INV 环境配置（简版）

## 1) 安装系统依赖（Ubuntu/Debian）

```bash
sudo apt-get update
sudo apt-get install -y opam m4 bubblewrap pkg-config libgmp-dev z3 build-essential
```

## 2) 创建 Conda 环境

```bash
cd /path/to/SAM2INV
conda env create -f environment.yml
conda activate sam2inv
```

## 3) 初始化 OPAM 并安装依赖

```bash
opam init --disable-sandboxing -y
eval "$(opam env)"

opam switch create sam2inv ocaml-base-compiler.4.14.2
eval "$(opam env --switch=sam2inv --set-switch)"

cd /path/to/SAM2INV
opam install -y . --deps-only
```

备用安装方式：

```bash
opam install -y $(grep -vE '^\s*#|^\s*$' opam-packages.txt)
```

## 4) 日常使用前激活

```bash
conda activate sam2inv
source src/scripts/opam.sh sam2inv
```

## 5) 验证环境

```bash
python --version
frama-c -version
why3 --version
alt-ergo --version
z3 --version
```

最小运行验证：

```bash
cd /path/to/SAM2INV/src
python3 loop_inv.py 1 --input-subdir NLA_lipus --max-iterations 1
```

## 6) 临时环境验证并删除

完整验证（严格按 `environment.yml`）：

```bash
TMP_ENV=/tmp/sam2inv_tmp_verify
conda env create -p "$TMP_ENV" -f environment.yml
conda activate "$TMP_ENV"
python -c "import numpy, openai, yaml, z3; print('ok')"
conda deactivate
conda env remove -p "$TMP_ENV" -y
```

如果网络下重包安装不稳定，可用轻量验证：

```bash
TMP_ENV=/tmp/sam2inv_tmp_verify
conda create -p "$TMP_ENV" -y python=3.11.14 pip
conda activate "$TMP_ENV"
pip install numpy openai pyyaml z3-solver fastapi uvicorn pydantic
python -c "import numpy, openai, yaml, z3, fastapi, uvicorn, pydantic; print('ok')"
conda deactivate
conda env remove -p "$TMP_ENV" -y
```
