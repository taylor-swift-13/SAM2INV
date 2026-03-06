# Loop Factory 数据构建流程（实现级说明）

本文档对应当前实现：
- `/home/yangfp/SAM2INV/loop_factory/batch_pipeline.py`
- `/home/yangfp/SAM2INV/loop_factory/generate_dpo_spec.py`

架构定位：
- **生成部分**是底座（程序生成 + 候选生成/过滤/验证）
- **batch_pipeline** 外挂在生成部分之上，负责从生成过程提取偏好数据与训练样本
- **质量门控**独立于生成部分，属于后处理准入

---

## 0. 总体分层

```
第1层 生成部分（Generation）
  A. 原始程序生成（loop_factory.py）
  B. 不变量候选生成、过滤、验证（InvariantGenerator + Frama-C/Houdini）

第2层 batch_pipeline 外挂提取层（Extraction on Generation）
  C. 从生成过程抽取偏好对（chosen/rejected）与对话对（distill）
  D. 数据写盘（SFT / DPO Teacher / DPO Aug / Distill）

第3层 后处理（Post-Generation）
  E. 质量门控（LLM quality gate）   <- 独立于生成部分
  F. 二阶段 spec 构建（generate_dpo_spec.py）
```

注：上面是职责分层。实际执行时序仍是  
`生成 -> 质量门控 -> batch_pipeline 提取并写盘`（其中质量门控虽由 batch_pipeline 调用，但语义上不属于生成部分）。

---

## 1. 生成部分 A：原始程序生成（`loop_factory.py`）

### 1.1 入口

`batch_pipeline.py` 在 `run_one_attempt(...)` 里调用：
- `generate_one_loop(...)`
- 内部执行 `loop_factory.py` 命令行生成 `*.c`

### 1.2 生成参数来源

参数来自三处合并：
1. `loop_factory_hyperparams(...)` 默认值  
2. `LOOP_FACTORY_USER_CONFIG`（`src/config.py`）  
3. CLI 覆盖（`batch_pipeline.py` 的 `--lf-*` 选项）

核心参数包括：
- 复杂度：`max_vars/max_params/min_params/max_assign/max_ifelse/max_depth`
- 结构：`min_loops/max_loops/p_multi/q_nest`
- 语义：`p_nonlinear/p_semantic_core/allowed_templates`

### 1.3 模板平衡与可用核心

在 `main()` 里先执行：
- `probe_usable_semantic_cores(...)`
- `build_even_core_plan(...)`

作用：
- 先探测当前参数下“可生成”的语义 core
- 按 attempt 数量平均分配配额，避免数据被少数模板主导

### 1.4 种子与并发

- 每个 attempt 使用独立随机 seed（非线性递增）
- 使用 `ThreadPoolExecutor(max_workers=args.workers)` 并发运行 attempt
- append 模式下会对 seed 流做偏移，减少与历史样本重叠

### 1.5 生成阶段硬拒绝

原始代码阶段会直接拒绝：
- 包含 `/*@ assert ... */` 的输入（`input has assert`）
- 未生成到有效 `.c` 文件

---

## 2. 生成部分 B：候选不变量生成、过滤、验证（`InvariantGenerator`）

`run_one_attempt(...)` 创建 `InvariantGenerator` 后执行：
- `gen.generate_all(max_iterations=1)`

该阶段本质是“候选集 -> 过滤 -> 合并 -> 验证 -> 最终注解”。

### 2.1 候选并发生成

`inv_generator.py` 内部按配置生成多组 candidate（`num_candidates`）：
- 通过 `_generate_multiple_candidates(...)` 并发调用 LLM
- 每个 candidate 是一份完整注解代码（包含 loop invariants）

### 2.2 过滤链路（在生成阶段内）

对每个 candidate 的 invariants 依次做：
1. 语法/结构过滤（syntax gate）
2. 采样过滤（sampling gate）
3. 合并冲突处理（可选）
4. Houdini 剪枝（Frama-C 驱动）

说明：
- 这些都属于“生成阶段内部质量控制”，用于得到可验证候选
- 会记录 `dpo_reject_reasons`，后续用于 teacher DPO 的 rejected 来源

### 2.3 验证状态门槛

`batch_pipeline.py` 只接受：
- `first_pass["syntax"]` 非空
- `first_pass["valid"]` 非空

否则 attempt 记入 reject_log：`syntax/valid failed`

### 2.4 生成阶段产物

该阶段输出：
- `annotated`（最终候选注解代码，尚未经过质量门控）
- `loop_dpo_records`（包含 rejected_items）
- 对话捕获 `all_pairs`（用于 distill）

---

## 3. 质量门控（独立于生成部分）

这是**生成之后**的独立后处理步骤，不属于“生成部分”本身：
- 函数：`quality_gate(gen, raw_code, annotated, llm_cfg, logger)`
- 模型返回严格 JSON：`{"ok": bool, "reason": "..."}`

判断关注：
- 不变量是否非平凡
- 是否覆盖循环更新关系与关键变量
- 是否包含必要边界信息

门控失败：
- attempt 不进入 SFT/DPO/Distill 主数据写盘
- 仅在 reject_log 记录原因（如 `llm_gate_rejected`）

---

## 4. 数据写盘（门控通过后）

门控通过后进入聚合写盘阶段，统一使用：
- `instruction = system_prompt`
- `input = user_prompt`
- `chosen = annotated`

### 4.1 SFT（`llama_factory_train_iio_api_aligned.jsonl`）

每个 accepted 样本写 1 条：

```json
{"instruction":"...","input":"...","output":"<annotated>"}
```

### 4.2 DPO Teacher（`llama_factory_train_dpo_teacher.jsonl`）

来源：`loop_dpo_records[*].rejected_items`  
每个 rejected 写 1 条：

```json
{"instruction":"...","input":"...","chosen":"<annotated>","rejected":"<teacher_reject>"}
```

### 4.3 DPO Aug（`llama_factory_train_dpo_aug.jsonl`）

三类增强混写到同一文件：

- A：Houdini 细粒度失败组合增强  
  `rej_code -> _aug_houdini_rejects(...)`

- B：正确解弱化子集（仅来自 chosen）  
  从 chosen 的不变量中随机取真子集，作为“弱正确但不充分”的 rejected

- C：错误候选随机子集  
  从老师错误 `rej_code` 的不变量随机取真子集作为 rejected

统一格式：

```json
{"instruction":"...","input":"...","chosen":"<annotated>","rejected":"<aug_reject>"}
```

### 4.4 Distill（`llama_factory_train_distill_sft.jsonl`）

来源：线程内劫持 `Chatbot.chat` 捕获到的 `all_pairs`。  
仅保留代码生成型对话，写入：

```json
{"instruction":"...","input":"<captured_prompt>","output":"<captured_response>"}
```

### 4.5 其它产物

- `raw/*.c`、`annotated/*.c`
- `file_template_map.jsonl`
- `logs/reject_log.json`

---

## 5. 去重与一致性

### 5.1 样本级去重

- `compute_loop_skeleton_key(raw_code)` 限制骨架重复（`max_skeleton_repeat`）

### 5.2 rejected 去重

- 单个 accepted 样本内使用 `seen_rejected`
- 跳过 `rejected == chosen`

### 5.3 chosen 一致性

- teacher 与 aug 对同一 accepted 样本始终共享同一个 chosen（最终 annotated）

---

## 6. `generate_dpo_spec.py`：二阶段 spec 数据构建

这个脚本不在 `batch_pipeline` 主链路里自动执行（当前默认未启用），是独立后处理管线：

1. 读取已有 DPO 文件（含 instruction/input/chosen/rejected）
2. 用 `instruction + input` 再调用模型生成一版 `generated`
3. 对 `generated` 跑一次 Frama-C 验证（`OutputVerifier`）
4. 仅保留验证失败样本写入新的 spec DPO JSONL

用途：
- 在原始 DPO 基础上再构造“模型实际会犯错”的 spec 负样本
- 常用于二阶段训练或数据再清洗

---

## 7. 一次完整样本的时序（简化）

1. attempt 生成 raw loop 程序  
2. 生成多 candidate invariants  
3. syntax/sampling/Houdini 过滤与验证  
4. 得到 annotated（生成阶段产物）  
5. 独立质量门控  
6. 门控通过后写入 SFT、DPO teacher、DPO aug、distill  
7. 记录 template map 与 reject_log

---

## 8. 当前边界

1. 质量门控失败样本不进入主数据文件（只在 reject_log 有记录）
2. `generate_dpo_spec.py` 是独立脚本，默认不由 `batch_pipeline` 自动调用
3. 子集增强在不变量数过少时会自然跳过
