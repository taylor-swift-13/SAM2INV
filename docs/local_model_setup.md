# 本地模型服务配置指南

本项目内置了一套基于 HuggingFace Transformers 的 OpenAI 兼容 HTTP 服务，
可在本机 GPU 上部署任意 causal LM，并通过与云端服务商完全相同的接口调用。

---

## 目录

1. [前置依赖](#1-前置依赖)
2. [配置 config.py](#2-配置-configpy)
3. [启动本地服务](#3-启动本地服务)
4. [切换到本地模式](#4-切换到本地模式)
5. [验证服务是否就绪](#5-验证服务是否就绪)
6. [多实例（多 GPU）场景](#6-多实例多-gpu-场景)
7. [查看日志 / 停止服务](#7-查看日志--停止服务)
8. [常见问题](#8-常见问题)

---

## 1. 前置依赖

```bash
pip install torch transformers fastapi uvicorn pydantic
```

GPU 建议：单实例至少需要能装下模型的显存（float16 精度，`device_map="auto"` 自动多卡分配）。

---

## 2. 配置 config.py

在 `src/config.py` 底部找到 `LOCAL_MODEL_SERVICE_CONFIG`，填写模型路径和实例数：

```python
LOCAL_MODEL_SERVICE_CONFIG = {
    # 必填：本地模型目录（HuggingFace 格式，含 config.json）
    'model_path': '/data/models/Qwen2.5-7B-Instruct',

    # 启动几个独立实例，分别占用 8001, 8002, ... 端口
    # 单卡建议 1；多卡或多机可设为 2+
    'num_instances': 1,
}
```

> **注意**：所有实例加载同一份模型，适合同一台机器上多 GPU 各跑一份的场景。

---

## 3. 启动本地服务

```bash
cd /home/yangfp/SAM2INV
python3 src/scripts/start_local_services_from_config.py
```

启动成功后终端输出类似：

```
[started] port=8001 pid=12345 log=src/log/local_api_instances/instance_8001.log
http://127.0.0.1:8001/v1
```

服务以**后台进程**运行（`start_new_session=True`），关闭终端后继续运行。

服务固定参数：

| 参数 | 值 |
|------|----|
| served model name | `qwen-local` |
| 起始端口 | `8001`（第 n 个实例占 `8000+n`）|
| API Key | 环境变量 `OPENAI_API_KEY`，默认 `EMPTY` |
| 最大上下文长度 | `8192` tokens |

---

## 4. 切换到本地模式

编辑 `src/config.py` 中的 `LLMConfig` 默认值：

```python
@dataclass
class LLMConfig:
    use_local: bool = True                  # 切换为本地模式

    local_model: str = "qwen-local"         # 必须与启动脚本中的 served_model 一致
    local_api_key: str = "EMPTY"            # 与启动时 OPENAI_API_KEY 一致
    local_base_urls: str = "http://127.0.0.1:8001/v1"   # 多实例用逗号分隔
    # 例（2 个实例）：
    # local_base_urls: str = "http://127.0.0.1:8001/v1,http://127.0.0.1:8002/v1"
```

切换回云端服务商时只需把 `use_local` 改回 `False`，其余配置不受影响。

---

## 5. 验证服务是否就绪

等待模型加载完毕（日志出现 `Model loaded.`），再执行：

```bash
curl http://127.0.0.1:8001/v1/models \
  -H "Authorization: Bearer EMPTY"
```

期望返回：

```json
{"object": "list", "data": [{"id": "qwen-local", "object": "model"}]}
```

发一条测试请求：

```bash
curl http://127.0.0.1:8001/v1/chat/completions \
  -H "Authorization: Bearer EMPTY" \
  -H "Content-Type: application/json" \
  -d '{
    "model": "qwen-local",
    "messages": [{"role": "user", "content": "hello"}],
    "max_tokens": 64
  }'
```

---

## 6. 多实例（多 GPU）场景

设置 `num_instances: 2`，启动脚本会在 8001、8002 各起一个进程。
在 `LLMConfig` 里用逗号分隔所有 URL，请求自动轮询（round-robin）：

```python
local_base_urls: str = "http://127.0.0.1:8001/v1,http://127.0.0.1:8002/v1"
```

如需控制每个实例使用哪块 GPU，在启动前设置环境变量：

```bash
CUDA_VISIBLE_DEVICES=0 python3 src/scripts/local_openai_service.py \
  --model-path /data/models/Qwen2.5-7B-Instruct --port 8001 &

CUDA_VISIBLE_DEVICES=1 python3 src/scripts/local_openai_service.py \
  --model-path /data/models/Qwen2.5-7B-Instruct --port 8002 &
```

（单独启动时跳过 `start_local_services_from_config.py` 即可。）

---

## 7. 查看日志 / 停止服务

**查看日志**：

```bash
tail -f src/log/local_api_instances/instance_8001.log
```

**停止服务**（根据 pid 文件）：

```bash
kill $(cat src/log/local_api_instances/instance_8001.pid)
```

**停止所有实例**：

```bash
for f in src/log/local_api_instances/*.pid; do
  kill $(cat "$f") 2>/dev/null && echo "stopped $f"
done
```

---

## 8. 常见问题

**模型加载很慢？**
首次加载需要从磁盘读取全部权重，7B 模型约需 1-3 分钟。可通过 `tail -f` 观察日志确认进度。

**`Unknown model` 错误？**
请求里的 `model` 字段必须与 `served_model_name` 完全一致，默认为 `"qwen-local"`。
检查 `LLMConfig.local_model` 是否也是 `"qwen-local"`。

**OOM / CUDA out of memory？**
减小 `max_model_len`，或使用量化版本（如 GPTQ/AWQ）的模型，或增加 `num_instances` 改用多卡分摊（模型在单卡内存不足时 `device_map="auto"` 会自动跨卡）。

**端口被占用？**
```bash
lsof -i :8001
```
找到 PID 后 `kill <pid>`。
