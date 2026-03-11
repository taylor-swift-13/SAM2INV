---
name: loop-curation-verify
description: 从 generated/test|teacher 标注 C 文件中筛选“有现实语义”的循环样本，补充非平凡 ACSL 后条件并验证。仅保留 Validate 全 True 且 Verify 通过的文件，用于扩展 curated 语义循环数据集。
---

# Loop Curation Verify

用于在 `loop_factory/generated/curated_semantic_loops` 中持续扩展高质量循环样本。

## 核心原则（必须满足）

1. 语义优先：样本应可映射到现实任务（计数/预算/库存/阈值控制/分段策略等）。
2. 后条件必加：每个新增文件都要在循环后添加非平凡 `/*@ assert ... */`。
3. 先验后留：验证通过才保留；失败直接删除该新增文件。
4. 不改程序逻辑：除注释（invariant/assert）外，不改 C 执行语义。

## Workflow（工作流程）

1. 选择候选循环（优先 `teacher/annotated`，可按用户要求仅 teacher）。
2. 复制到 curated 目录，命名为 `teacher_<id>.c` 或 `test_<id>.c`。
3. 检查并整理循环不变量（删除明显文本重复）。
4. 在循环结束后添加非平凡后条件 `/*@ assert ... */`。
5. 运行验证；仅保留满足：
   - `Validate` 全 `True`
   - `Verify` 为 `[]` 或全 `True`
6. 更新 `README.md` 的 source mapping。
7. 做噪声回检（弱语义循环标记或移除）。

## Candidate Selection（候选筛选）

优先：

- 有分支决策（`if/else`）且体现策略切换。
- 有守卫边界（如 `x<n`, `q>0`, `i<=m-1`）。
- 有结构化递推（累加、倍增、分段更新、模约束）。
- 可解释为现实过程：
  - 计数统计
  - 资源消耗/库存变化
  - 预算更新
  - 阈值触发行为

避免：

- 无分支 + 无模约束 + 仅弱线性边界的“噪声循环”。
- 验证反复超时且难以修复的超重样本。

## Postcondition Rules（后条件规则）

新增 `assert` 必须满足：

1. 体现循环结束后的全局状态，而非中间状态。
2. 至少包含一条“退出条件 + 状态关系”的组合性质。
3. 不允许仅 `assert true` 或纯平凡边界。
4. 推荐模式：
   - 退出条件：如 `q <= 1`, `e + 2 > i`, `l >= m`。
   - 保持关系：如同余关系、单调关系、与 `\at(..., Pre)` 的映射关系。
   - 结果性质：如最终计数关系、资源非负、分段结果条件。

## Commands（命令）

### 1）复制样本

```bash
cp loop_factory/generated/teacher/annotated/<id>.c loop_factory/generated/curated_semantic_loops/teacher_<id>.c
cp loop_factory/generated/test/annotated/<id>.c loop_factory/generated/curated_semantic_loops/test_<id>.c
```

### 2）去重（文本级 invariant 去重）

```bash
python3 .codex/skills/loop-curation-verify/scripts/dedup_invariants.py \
  --dir /home/yangfp/SAM2INV/loop_factory/generated/curated_semantic_loops
```

### 3）验证（项目标准）

```bash
python3 .codex/skills/loop-curation-verify/scripts/verify_curated_loops.py \
  --dir /home/yangfp/SAM2INV/loop_factory/generated/curated_semantic_loops \
  --src /home/yangfp/SAM2INV/src \
  --timeout-sec 90
```

### 4）单文件快速验证（建议并行）

```bash
python3 -c "import sys; sys.path.insert(0,'/home/yangfp/SAM2INV/src'); from output_verify import OutputVerifier; v=OutputVerifier(output=False); v.run('/abs/path/file.c'); print(v.validate_result, v.verify_result)"
```

## Editing Rules（编辑约束）

- 不改原始 C 语句执行逻辑。
- `loop invariant` 写在循环注释块 `/*@ ... */` 内。
- `assert` 必须写在循环后。
- 仅参数使用 `\at(..., Pre)`。
- 优先语义关系（代数/分段/同余/守卫关联），避免空泛约束。

## Verification & Keep/Drop Policy

- 保留：`Validate` 全 True 且 `Verify` 通过。
- 删除：任一 invariant/assert 不可证，或稳定超时。
- 若去重后出现回归，回滚该文件去重结果并重新验证。

## Noise Audit（噪声回检）

定期检查 curated：

- 单循环 + 无分支 + 无模约束 + invariant 过少（例如 <=4）
- 仅弱边界，无可解释业务语义

命中样本标为“疑似噪声”，优先替换。

## Output Expectations（每轮输出）

1. 新增文件列表（含来源 ID）。
2. 每个新增文件的后条件摘要（说明语义含义）。
3. 验证结果：`Validate` / `Verify`。
4. 被删除文件及原因（不可证/超时/噪声）。
5. 当前规模统计（teacher/test/total）。
