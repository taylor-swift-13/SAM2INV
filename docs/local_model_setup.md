# 本地 Transformers 配置指南

本项目已移除 vLLM，仅支持本地 `Transformers` 推理或云端 API。

## 1. 安装依赖

```bash
pip install torch transformers
```

## 2. 配置本地模型

编辑 `src/config.py` 的 `LLMConfig`：

```python
@dataclass
class LLMConfig:
    use_local: bool = True
    local_model_path: str = "/path/to/your/hf-model"
```

说明：
- `local_model_path` 必须指向 HuggingFace 格式模型目录（包含 `config.json`）。
- 关闭本地模式时，设置 `use_local=False`，继续使用 `api_model/api_key/base_url`。

## 3. 验证

```bash
cd /home/yangfp/SAM2INV/src
python3 - <<'PY'
from config import LLMConfig
from llm import Chatbot
cfg = LLMConfig(use_local=True, local_model_path="/path/to/your/hf-model")
bot = Chatbot(cfg)
print(type(bot.llm_instance).__name__)
PY
```

若输出 `TransformersLLMImpl`，说明配置生效。
