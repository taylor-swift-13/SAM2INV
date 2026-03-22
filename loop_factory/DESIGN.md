下面是**完整、可直接使用的 Markdown 文档**。结构已经按照论文 Method / Data Generation Section 排好，包含：

* 完整 DSL 定义
* 概率分布建模
* 递归生成算法
* 联合概率因子分解
* 期望规模分析
* 设计合理性说明

你可以直接复制到论文或技术报告中。

---

# Probabilistic DSL-Based Numeric Loop Synthesis

## 1. Overview

We define a probabilistic domain-specific language (DSL) for synthesizing structured numeric programs containing:

* Linear and non-linear arithmetic
* Modular arithmetic
* Structured nested loops (loop forest)
* Controlled initialization discipline
* Fully parameterized probability distributions

The generator defines a well-formed probability distribution over a family of numeric loop programs.

---

# 2. Hyperparameters

Let the generation parameters be:

[
\theta =
(m, p, n, k, D_{\max},
\pi_{\text{op}},
\pi_{\text{cmp}},
\pi_{\text{const}},
\pi_{\text{self}},
\pi_{\text{nest}})
]

Where:

| Symbol               | Meaning                                    |
| -------------------- | ------------------------------------------ |
| (m)                  | Maximum number of variables                |
| (p)                  | Number of parameter variables              |
| (n)                  | Number of top-level loops                  |
| (k)                  | Max assignments per loop                   |
| (D_{\max})           | Max nesting depth                          |
| (\pi_{\text{op}})    | Distribution over arithmetic operators     |
| (\pi_{\text{cmp}})   | Distribution over comparison operators     |
| (\pi_{\text{const}}) | Probability of sampling a constant operand |
| (\pi_{\text{self}})  | Probability of self-update assignment      |
| (\pi_{\text{nest}})  | Probability of generating nested loops     |

---

# 3. Variable Model

## 3.1 Variable Sampling

Sample number of variables:

[
V \sim \text{Uniform}(2, m)
]

Construct variable set:

[
\mathcal{V} = {v_1, \dots, v_V}
]

Sample parameter subset:

[
\mathcal{P} \subset \mathcal{V}, \quad |\mathcal{P}| = p
]

Writable variables:

[
\mathcal{L} = \mathcal{V} \setminus \mathcal{P}
]

---

# 4. DSL Syntax

## 4.1 Arithmetic Expressions

[
e ::= v
\mid c
\mid v ;\texttt{op}; x
]

Where:

* (v \in \mathcal{V})
* (c \in \mathbb{Z})
* (x \in \mathcal{V} \cup \mathbb{Z})
* (\texttt{op} \in {+, -, *, /, \bmod})

Constraint:

If (\texttt{op} = \bmod), RHS must be a positive integer constant.

---

## 4.2 Boolean Expressions

[
b ::= e_1 ;\texttt{cmp}; e_2
]

Where:

[
\texttt{cmp} \in {<, \le, >, \ge, =, \neq}
]

---

## 4.3 Assignment Statements

[
s ::= v := e, \quad v \in \mathcal{L}
]

---

# 5. Program Structure

## 5.1 Overall Form

[
\textbf{Prog} ::= \textbf{InitBlock} ; \textbf{LoopForest}
]

---

## 5.2 Initialization Block

For every writable variable:

[
\forall v \in \mathcal{L}, \quad \exists!; v := e
]

Constraint:

[
\mathrm{FV}(e) \subseteq \mathcal{P}
]

This guarantees all writable variables are initialized exactly once before loops.

---

## 5.3 Loop Forest

[
\mathcal{F} = [T_1, T_2, \dots, T_n]
]

Top-level loops execute sequentially.

---

## 5.4 Loop Tree Node

[
T = \langle b, S, \mathcal{C} \rangle
]

Where:

* (b): loop guard
* (S): assignment list (|S| ≤ k)
* (\mathcal{C}): nested loops

Depth constraint:

[
\text{depth}(T) \le D_{\max}
]

---

# 6. Execution Semantics

For loop node (T = \langle b, S, \mathcal{C} \rangle):

```
while b do
    execute S
    for each T' in C:
        execute T'
```

Subloops execute after the parent body.

---

# 7. Probabilistic Generation

## 7.1 Operand Sampling

At any operand position:

[
x \sim
\begin{cases}
\text{Const} & \text{w.p. } \pi_{\text{const}} \
\text{Var}(\mathcal{V}) & \text{w.p. } 1 - \pi_{\text{const}}
\end{cases}
]

---

## 7.2 Operator Sampling

[
\texttt{op} \sim \text{Categorical}(\pi_{\text{op}})
]

---

## 7.3 Comparison Sampling

[
\texttt{cmp} \sim \text{Categorical}(\pi_{\text{cmp}})
]

---

## 7.4 Self-Update Modeling

For assignment (v_i := e):

[
e =
\begin{cases}
v_i ;\texttt{op}; x & \text{w.p. } \pi_{\text{self}} \
v_j ;\texttt{op}; x & \text{w.p. } 1 - \pi_{\text{self}}
\end{cases}
]

Where (v_j \ne v_i).

---

## 7.5 Loop Nesting Probability

At depth (d):

[
\Pr(\text{generate children}) =
\begin{cases}
\pi_{\text{nest}} & d < D_{\max} \
0 & d = D_{\max}
\end{cases}
]

---

# 8. Full Generative Distribution

The probability of a program factorizes as:

[
\Pr(\textbf{Prog}) =
\prod_{v \in \mathcal{L}} \Pr(v := e)
\cdot
\prod_{T \in \mathcal{F}} \Pr(T)
]

Recursively:

[
\Pr(T) =
\Pr(b)
\cdot
\prod_{s \in S} \Pr(s)
\cdot
\prod_{T' \in \mathcal{C}} \Pr(T')
]

This defines a well-formed probability distribution over loop forests.

---

# 9. Expected Structural Properties

## Expected Nesting Depth

If nesting follows a Bernoulli process:

[
\mathbb{E}[\text{depth}] =
\sum_{d=0}^{D_{\max}} d \cdot
(1-\pi_{\text{nest}})\pi_{\text{nest}}^d
]

---

## Expected Assignments per Loop

If assignment count sampled uniformly:

[
\mathbb{E}[|S|] = \frac{k+1}{2}
]

---

## Expected Total Loop Nodes

If each node independently spawns children:

[
\mathbb{E}[\text{#nodes}] =
\sum_{d=0}^{D_{\max}} \pi_{\text{nest}}^d
]

---

# 10. Properties

The synthesis method guarantees:

* Structured control flow
* No undefined variables
* Controlled nesting depth
* Tunable linear vs nonlinear ratio
* Modular arithmetic support
* Explicit probability model
* Factorizable joint likelihood

---

# 11. Design Rationale

The explicit probabilistic formulation provides:

* Controlled structural diversity
* Adjustable arithmetic complexity
* Fine-grained ablation capability
* Compatibility with likelihood-based analysis
* A principled synthetic benchmark distribution

This makes the generator suitable for:

* Program analysis benchmarking
* Loop invariant learning
* Symbolic reasoning evaluation
* Reinforcement learning over structured programs

---

# 12. LLM-Guided Semantic Diversification

While the probabilistic DSL provides strong control over structural variation, template-level diversity can still become narrow when a fixed semantic core is instantiated only through hand-written operator rules. To address this, we augment the generator with a semantic-core-conditioned large language model (LLM) stage.

## 12.1 Motivation

The DSL already controls:

* loop counts and nesting depth,
* arithmetic operator mixtures,
* branch frequency,
* parameter and state-variable budgets.

However, these controls do not fully capture diversity *within* a given semantic pattern. For example, two loops may both implement prefix-style accumulation or quotient-remainder reduction, yet differ substantially in:

* guard structure,
* state-role allocation,
* update ordering,
* auxiliary shadow variables,
* conditional refinement logic.

These intra-template variations are difficult to enumerate exhaustively using only manually designed DSL branches. We therefore use an LLM to expand the realization space of each semantic core while preserving its intended meaning.

## 12.2 Semantic-Core-Conditioned Generation

For each selected semantic core \(c\), we define a natural-language specification
\(\sigma(c)\) that describes:

* the intended loop semantics,
* mandatory state-transition properties,
* admissible implementation variations,
* forbidden degeneracies.

Examples include:

* prefix-style progress with one or more meaningful accumulators,
* snapshot/shadow-state synchronization,
* quotient-remainder style reduction,
* Euclid-like coupled descent,
* multiplicative decomposition via doubling/halving.

Instead of allowing the DSL alone to instantiate the loop body, we first query an LLM with \(\sigma(c)\) together with the currently available variable set, loop-control variables, and complexity budget. The model returns a structured loop fragment consisting of:

* a guard,
* optional initialization overrides,
* assignment statements,
* optional conditional branches.

This fragment is then converted back into the internal loop AST used by the generator.

## 12.3 Constrained Decoding and Safety

The LLM is not allowed to emit arbitrary code. It is constrained by:

* a fixed variable vocabulary supplied by the generator,
* a bounded number of assignments and conditional nodes,
* a restricted statement grammar,
* semantic-core-specific validation rules.

The emitted fragment is accepted only if it satisfies static checks such as:

* all variables belong to the permitted set,
* the generated loop exhibits explicit progress,
* the statement budget is respected,
* the fragment preserves the required semantic roles of the target core.

If any check fails, the system falls back to the original hand-written DSL realization. Therefore, the LLM acts as a semantic diversification layer rather than a replacement for the base generator.

## 12.4 Effect on Diversity

This hybrid design increases diversity along dimensions that are hard to enumerate manually:

* alternative guard formulations,
* different allocations of accumulator, shadow, and control variables,
* reordered yet semantically equivalent update sequences,
* richer branch-conditioned realizations of the same semantic motif,
* multiple concrete realizations for the same benchmark-aligned template.

Crucially, the diversity introduced by the LLM is not intended to be merely lexical. It is semantic-core-preserving diversity: samples differ in operational realization while remaining aligned with a common interpretable loop pattern.

## 12.5 Role in the Data Pipeline

In the full data-generation pipeline, the LLM-guided stage operates before invariant generation and verification:

```text
semantic core selection
    -> LLM-guided loop realization
    -> AST validation / fallback
    -> raw C program synthesis
    -> invariant generation
    -> verification and quality filtering
```

This ordering is important. The LLM increases the support of the raw program distribution, while correctness and usefulness are still enforced downstream by invariant validation, verification, and data-quality filters.

## 12.6 Summary of the Hybrid Strategy

The final generator combines:

* a probabilistic DSL for global structural control, and
* an LLM-based semantic realization stage for local intra-core diversity.

This yields a practical compromise between analyzability and expressive coverage: the DSL preserves tractable control over the overall program family, while the LLM expands the diversity of meaningful implementations inside each semantic class.

---

# 13. Summary

We define a parameterized probabilistic DSL that generates structured numeric loop programs as a loop forest with bounded nesting depth. The model provides explicit operator distributions, constant injection control, self-update modeling, and stochastic loop nesting.

We further augment this DSL with an LLM-guided semantic diversification stage that expands intra-template variability while preserving semantic-core constraints. The resulting generator defines a tractable yet more expressive distribution over numeric programs.

