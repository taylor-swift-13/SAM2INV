# loop_factory

基于 `DESIGN.md` 的 DSL 循环合成器，输出风格对齐 `src/input/NLA_lipus`，并去掉 `requires/assert`。

## 特点

- 与 `src/input` 对齐的 C 代码风格：
  - `int mainX(int a,int b,...)`
  - 局部变量声明后初始化
  - 以 `while` 为核心控制流，可含 `if`
- 不生成 `requires` 和 `assert`
- 循环有明确语义模板（非纯随机更新）
- 基于 DSL AST 构建，支持扩展到多层循环

## 概率模型（你定义的 p/q）

- 每次生成都只有一棵循环树（单根 `while`）
- 额外循环概率 `p`：`P(L>=2)=p`, `P(L>=3)=p^2`（`L` 为树中循环节点数）
- 链式嵌套概率 `q`：按生成顺序，第 `i` 个循环以概率 `q` 嵌套到第 `i-1` 个循环中，否则挂到根循环下
- 硬约束：
  - 最大循环节点数：`--max-loops`
  - 最大嵌套深度：`--max-depth`
  - 当 `--max-depth 1` 时，始终只有一个循环节点

## 语义模板

- 三次增长递推（`x,y,z` 联动）
- 几何递推（`x = x*z + 1`, `y = y*z`）
- 累加型平方和/内积
- 幂和累加（`x += y^d`, `d in [1..5]`）
- 商余计数（`while (x > y*q + r)`）
- 二进制乘法风格（`while + if`）
- 线性双变量平移（`x += c, y += c`）
- 线性减到零（`while (x>0) x--`）
- 模分桶计数（按 `%2..%6` 条件链计数）
- 减法版 Euclid 循环（`while(x!=0 && y!=0)`）
- 嵌套三角和（两层 `while`）
- 嵌套仿射更新（两层 `while`）

## 使用

```bash
python3 loop_factory.py --profile benchmark --out-dir generated/NLA_prob --count 50 --seed 2026
```

## 生成更复杂的多层循环

```bash
python3 loop_factory.py \
  --profile rich \
  --out-dir generated/NLA_prob_rich \
  --count 100 \
  --seed 2026 \
  --params 3 \
  --max-loops 6 \
  --max-depth 2 \
  --p-multi 0.45 \
  --q-nest 0.15
```

输出为 `1.c`, `2.c`, ...，每个文件一个程序。
