# loop_factory

`loop_factory` 是 SAM2INV 的数据构造子系统，负责：
1. 生成循环程序（raw code）
2. 生成与筛选循环不变量候选
3. 合成训练数据（SFT / DPO / Distill / Spec）
4. 在最终写盘前做 COT 补齐与字段校验

---

## 目录里有什么

核心脚本：
1. `loop_factory.py`：原始 C 循环程序生成器（模板/语义核心驱动）
2. `batch_pipeline.py`：主流程（从 raw code 到训练 JSONL）
3. `one_sample_pipeline.py`：单样本调试流程
4. `sft_pipeline.py`：SFT 相关实验流程
5. `generate_distill.py`：独立 Distill 数据构造
6. `generate_dpo_spec.py`：独立 Spec-DPO 数据构造（待优化模型失败样本）
7. `reverse_cot.py`：逆向 COT 生成与拼接工具

常见产物目录：
1. `generated/<work_dir>/raw`：原始程序
2. `generated/<work_dir>/annotated`：最终注解程序
3. `generated/<work_dir>/logs`：运行日志与 reject 记录
4. `generated/<work_dir>/*.jsonl`：训练数据文件

---

## 整体数据流（简版）

```text
Raw Code
 -> 候选不变量生成（多候选）
 -> 过滤/验证/合并
 -> Final Annotated
 -> 质量门控
 -> 训练数据合成：
    - SFT
    - DPO Teacher（错误组）
    - DPO Aug（增强组）
    - Distill
    - DPO Spec（独立脚本，可选）
 -> COT 注入/补齐
 -> 字段校验
 -> Final JSONL
```

---

## 训练数据文件说明

在 `generated/<work_dir>/` 下，主流程会生成：

1. `llama_factory_train_iio_api_aligned.jsonl`
- SFT 数据：`instruction/input/output`

2. `llama_factory_train_dpo_teacher.jsonl`
- DPO 错误组：`instruction/input/chosen/rejected`

3. `llama_factory_train_dpo_aug.jsonl`
- DPO 增强组：`instruction/input/chosen/rejected`

4. `llama_factory_train_distill_sft.jsonl`
- Distill 数据：`instruction/input/output`

5. `file_template_map.jsonl`
- 样本与模板核心映射关系

6. `logs/reject_log.json`
- 失败样本与拒绝原因

---

## 快速开始

## 1) 仅生成 raw 程序

```bash
cd /home/yangfp/SAM2INV/loop_factory
python3 loop_factory.py --profile benchmark --out-dir generated/demo --count 50 --seed 2026
```

## 2) 运行主流程生成训练数据

```bash
python3 batch_pipeline.py \
  --work-dir test \
  --target-count 100 \
  --workers 20 \
  --num-candidates 5 \
  --append
```

## 3) 只对已有数据执行 COT 阶段（不新增样本）

```bash
python3 batch_pipeline.py --work-dir test --target-count 0 --append
```

---

## 常用参数（主流程）

运行规模：
1. `--target-count`：目标样本数
2. `--max-attempts`：最大尝试次数
3. `--workers`：并发 worker 数
4. `--num-candidates`：每次候选数
5. `--append/--no-append`：追加或重建

复杂度与结构：
1. `--max-vars --min-vars`
2. `--max-params --min-params`
3. `--min-loops --max-loops`
4. `--max-assign --min-assign`
5. `--max-ifelse --min-ifelse`
6. `--max-depth`
7. `--p-multi --q-nest`
8. `--p-nonlinear --p-semantic-core`
9. `--allowed-templates`

模型相关：
1. `--model`

---

## COT 相关约束

主流程最终会对训练输出字段执行 COT 处理与校验：
1. 组合字段：强制 reverse-COT
2. 直出字段：优先原生 COT，缺失则补齐
3. 写盘前字段校验：`output/chosen/rejected` 必须包含 COT 标签

如果你只想对历史文件补 COT，请使用：
`--target-count 0 --append`

---

## 常见问题排查

1. 训练文件里没有 COT
- 先确认流程是否完整结束（有最终写盘日志）
- 再检查字段覆盖率（`output/chosen/rejected`）
- 若中途中断，执行一次 `--target-count 0 --append`

2. 样本很少或拒绝很多
- 提高 `max-attempts`
- 放宽结构复杂度参数
- 检查模板限制 `--allowed-templates` 是否过窄

3. DPO aug 很少
- 检查增强开关与 rejected 来源是否充足
- 检查去重是否过强

---

## 相关文档

1. `DESIGN.md`：更广泛的设计说明
