#!/usr/bin/env python3
from __future__ import annotations

import argparse
import random
from dataclasses import dataclass
from pathlib import Path
from typing import List, Sequence, Tuple


@dataclass(frozen=True)
class HyperParams:
    m: int = 10
    p: int = 3
    min_while_fuel: int = 0
    while_fuel: int = 3         # program-level upper bound for while loops
    assign_fuel: int = 6        # per-loop assign upper bound (including loop-step)
    ifelse_fuel: int = 4        # per-loop if/if-else upper bound (kept for compatibility)
    d_max: int = 2
    p_multi: float = 0.35
    q_nest: float = 0.12
    p_nonlinear: float = 0.55   # probability a loop is NLA-like family
    nonlinear_strength: float = 0.60
    p_semantic_core: float = 0.50
    w_core_rel_guard: float = 1.0
    w_core_cond_fixed: float = 1.0
    w_core_linear_state: float = 1.0


class Stmt:
    def render(self, indent: int = 0) -> List[str]:
        raise NotImplementedError


@dataclass(frozen=True)
class Assign(Stmt):
    target: str
    expr: str

    def render(self, indent: int = 0) -> List[str]:
        return [f"{' ' * indent}{self.target} = {self.expr};"]


@dataclass(frozen=True)
class IfOnly(Stmt):
    cond: str
    then_body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}if ({self.cond}) {{"]
        for s in self.then_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass(frozen=True)
class IfElse(Stmt):
    cond: str
    then_body: List[Stmt]
    else_body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}if ({self.cond}) {{"]
        for s in self.then_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        out.append(f"{pad}else {{")
        for s in self.else_body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass(frozen=True)
class WhileLoop(Stmt):
    cond: str
    body: List[Stmt]

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        out = [f"{pad}while ({self.cond}) {{"]
        for s in self.body:
            out.extend(s.render(indent + 4))
        out.append(f"{pad}}}")
        return out


@dataclass
class Program:
    name: str
    params: List[str]
    local_inits: List[Tuple[str, str]]
    body: List[Stmt]

    def render(self) -> str:
        sig = ",".join(f"int {p}" for p in self.params)
        lines = [f"int {self.name}({sig}){{"]
        if self.local_inits:
            lines.append(f"  int {', '.join(v for v, _ in self.local_inits)};")
            lines.append("")
            for v, e in self.local_inits:
                lines.append(f"  {v}={e};")
            lines.append("")

        for s in self.body:
            lines.extend(s.render(2))
            lines.append("")

        lines.append("}")
        return "\n".join(lines)


class NameAllocator:
    def __init__(self, params: Sequence[str], rng: random.Random):
        self.used = set(params)
        self.rng = rng
        self.letters = list("abcdefghijklmnopqrstuvwxyz")

    def alloc(self, hint: str = "v") -> str:
        available = [x for x in self.letters if x not in self.used]
        if not available:
            raise RuntimeError("No available single-letter variable names remain")
        if hint and len(hint) == 1 and hint in available:
            name = hint
        else:
            name = self.rng.choice(available)
        self.used.add(name)
        return name

    def remaining(self) -> int:
        return len([x for x in self.letters if x not in self.used])


class ProbabilisticLoopFactory:
    def __init__(self, hp: HyperParams, rng: random.Random):
        self.hp = hp
        self.rng = rng
        self.param_candidates = ["a", "b", "k", "n", "m", "p", "q"]

    def _pick_params(self) -> List[str]:
        p = max(1, min(self.hp.p, len(self.param_candidates)))
        return sorted(self.rng.sample(self.param_candidates, k=p))

    def _sample_loop_count(self) -> int:
        # Fuel is an upper bound. Actual loop count is sampled in [0, while_fuel].
        lo = max(1, self.hp.min_while_fuel)
        hi = max(lo, self.hp.while_fuel)
        return self.rng.randint(lo, hi)

    def _sample_const(self) -> int:
        return self.rng.choice([-8, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 8])

    def _sample_operand(self, vars_pool: Sequence[str], allow_const: bool = True) -> str:
        if allow_const and self.rng.random() < 0.35:
            return str(self._sample_const())
        return self.rng.choice(list(vars_pool))

    def _sample_expr(self, target: str, vars_pool: Sequence[str], nla_family: bool) -> str:
        if self.rng.random() < 0.14:
            return self._sample_operand(vars_pool, allow_const=True)

        left = target if self.rng.random() < 0.6 else self.rng.choice(list(vars_pool))
        if nla_family:
            op = self.rng.choices(["+", "-", "*", "%"], weights=[0.25, 0.17, 0.46, 0.12], k=1)[0]
        else:
            op = self.rng.choices(["+", "-", "*", "%"], weights=[0.54, 0.34, 0.09, 0.03], k=1)[0]

        if op == "%":
            rhs = str(self.rng.randint(2, 11))
        else:
            rhs = self._sample_operand(vars_pool, allow_const=True)
            if rhs == "0" and op in {"+", "-"}:
                rhs = str(self.rng.randint(1, 6))

        if rhs.startswith("-"):
            rhs = f"({rhs})"
        return f"{left}{op}{rhs}"

    def _sample_limit_expr(self, src: str) -> str:
        # Diversify loop-limit initialization: constant, parameter, or simple affine/mod form.
        mode = self.rng.choices(
            ["const", "src", "src_plus", "src_minus", "src_mod"],
            weights=[0.28, 0.22, 0.24, 0.08, 0.18],
            k=1,
        )[0]
        if mode == "const":
            return str(self.rng.randint(8, 80))
        if mode == "src":
            return src
        if mode == "src_plus":
            return f"{src}+{self.rng.randint(3, 25)}"
        if mode == "src_minus":
            return f"{src}-{self.rng.randint(1, 10)}"
        base = self.rng.randint(6, 40)
        off = self.rng.randint(4, 20)
        return f"({src}%{base})+{off}"

    def _sample_loop_control(self, src: str, ctr: str, lim: str, nla_family: bool) -> Tuple[List[Tuple[str, str]], str, Assign]:
        lim_expr = self._sample_limit_expr(src)

        if nla_family:
            weights = [0.25, 0.15, 0.15, 0.25, 0.20]  # more mul/div styles
        else:
            weights = [0.48, 0.24, 0.20, 0.05, 0.03]  # mostly linear counters

        mode = self.rng.choices(["inc1", "dec1", "inc_step", "mul_up", "div_down"], weights=weights, k=1)[0]

        if mode == "inc1":
            return [(lim, lim_expr), (ctr, "0")], f"{ctr}<{lim}", Assign(ctr, f"{ctr}+1")
        if mode == "dec1":
            return [(lim, lim_expr), (ctr, lim)], f"{ctr}>0", Assign(ctr, f"{ctr}-1")
        if mode == "inc_step":
            d = self.rng.randint(2, 5)
            return [(lim, lim_expr), (ctr, "0")], f"{ctr}<{lim}", Assign(ctr, f"{ctr}+{d}")
        if mode == "mul_up":
            mul = self.rng.randint(2, 3)
            return [(lim, lim_expr), (ctr, "1")], f"{ctr}<{lim}", Assign(ctr, f"{ctr}*{mul}")
        return [(lim, lim_expr), (ctr, lim)], f"{ctr}>0", Assign(ctr, f"{ctr}/2")

    def _semantic_assign(self, tgt: str, peer: str, ctr: str, lim: str, vars_pool: Sequence[str], nla_family: bool) -> Assign:
        p = self.rng.random()
        if not nla_family:
            if p < 0.22:
                expr = f"{tgt}+1"
            elif p < 0.44:
                expr = f"{tgt}+{ctr}"
            elif p < 0.64:
                expr = f"{tgt}+{peer}"
            elif p < 0.80:
                expr = f"{peer}-{tgt}"
            elif p < 0.92:
                expr = f"{tgt}+{self.rng.randint(1, 6)}"
            else:
                expr = self._sample_expr(tgt, vars_pool + [lim], nla_family=False)
        else:
            s = max(0.0, min(1.0, self.hp.nonlinear_strength))
            weak = 0.32 * (1.0 - s)
            if p < weak:
                expr = f"{tgt}+{peer}" if self.rng.random() < 0.5 else f"{peer}+{ctr}"
            elif p < weak + 0.18:
                expr = f"{tgt}*2"
            elif p < weak + 0.36:
                expr = f"{peer}*{peer}"
            elif p < weak + 0.56:
                expr = f"{tgt}*{peer}"
            elif p < weak + 0.76:
                expr = f"{tgt}*{tgt}+{peer}"
            elif p < weak + 0.90:
                expr = f"{tgt}%{self.rng.randint(2, 9)}"
            else:
                expr = self._sample_expr(tgt, vars_pool + [lim], nla_family=True)
        return Assign(tgt, expr)

    def _sample_cond(self, ctr: str, lim: str, aux: str, vars_pool: Sequence[str], nla_family: bool) -> str:
        r = self.rng.random()
        if r < 0.30:
            return f"({ctr}%{self.rng.randint(2, 9)})==0"
        if r < 0.56:
            return f"{aux}+{self.rng.randint(1, 7)}<{lim}"
        if r < 0.80:
            v = self.rng.choice(list(vars_pool))
            return f"{ctr}+{self.rng.randint(1, 7)}<={v}+{lim}"
        if nla_family:
            v = self.rng.choice(list(vars_pool))
            return f"{v}*{v}<={lim}+{self.rng.randint(1, 6)}"
        v1 = self.rng.choice(list(vars_pool))
        v2 = self.rng.choice(list(vars_pool))
        return f"{v1}<{v2}+{self.rng.randint(1, 5)}"

    def _sample_state_vars(self, alloc: NameAllocator, nla_family: bool, max_count: int) -> List[str]:
        max_state = max(1, min(max_count, 8, alloc.remaining()))
        if nla_family:
            lo = 4 if max_state >= 4 else 1
            count = self.rng.randint(lo, max_state)
        else:
            hi = max(1, min(max_state, 6))
            count = self.rng.randint(1, hi)
        return [alloc.alloc("v") for _ in range(count)]

    def _seed_family_kernel(
        self,
        body: List[Stmt],
        writable: Sequence[str],
        ctr: str,
        assign_budget: int,
        nla_family: bool,
    ) -> int:
        used = 0
        if len(writable) < 3:
            return used

        if nla_family:
            # NLA-like recurrences
            a, b, c = writable[0], writable[1], writable[2]
            kernels = [
                [Assign(a, f"{a}+{b}"), Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{self.rng.randint(1, 6)}")],
                [Assign(a, f"{a}*2"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}%{self.rng.randint(2, 9)}")],
                [Assign(a, f"{a}+{ctr}"), Assign(b, f"{b}*{b}"), Assign(c, f"{c}+{a}*{b}")],
            ]
        else:
            # linear-like transitions
            a, b, c = writable[0], writable[1], writable[2]
            kernels = [
                [Assign(a, f"{a}+1"), Assign(b, f"{b}+{a}")],
                [Assign(a, f"{a}+{self.rng.randint(1, 5)}"), Assign(c, f"{c}+{self.rng.randint(1, 4)}")],
                [Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{a}")],
            ]

        k = self.rng.choice(kernels)
        for st in k:
            if used < assign_budget:
                body.append(st)
                used += 1
            else:
                break
        return used

    def _sample_core_loop(
        self,
        alloc: NameAllocator,
        params: Sequence[str],
        universe: List[str],
        remaining_local_budget: int,
    ) -> Tuple[List[Tuple[str, str]], WhileLoop, List[str]]:
        src = self.rng.choice(list(params)) if params else "1"
        nla_family = self.rng.random() < self.hp.p_nonlinear

        if remaining_local_budget < 3:
            raise ValueError("remaining_local_budget must be at least 3")

        ctr = alloc.alloc("i")
        lim = alloc.alloc("l")
        # Reserve 2 locals for loop control (ctr/lim), others for state vars.
        state_cap = max(1, remaining_local_budget - 2)
        state_vars = self._sample_state_vars(alloc, nla_family, state_cap)

        ctrl_inits, guard, step_stmt = self._sample_loop_control(src, ctr, lim, nla_family)
        init_pool = universe + list(params) + [ctr, lim]

        inits: List[Tuple[str, str]] = list(ctrl_inits)
        for sv in state_vars:
            inits.append((sv, self._sample_operand(init_pool, allow_const=True)))

        vars_pool = list(dict.fromkeys(universe + list(params) + state_vars + [ctr, lim]))

        # Per-loop sampled fuel:
        # - if/if-else blocks in [0, ifelse_fuel]
        # - assigns in [1, assign_fuel], with one assign reserved for loop-step
        if_budget = self.rng.randint(0, max(0, self.hp.ifelse_fuel))
        assign_total = self.rng.randint(1, max(1, self.hp.assign_fuel))

        body: List[Stmt] = []
        used_if = 0
        used_assign = 0
        append_step = True

        def set_init(name: str, expr: str) -> None:
            for i, (v, _) in enumerate(inits):
                if v == name:
                    inits[i] = (name, expr)
                    return

        # Generalized core rules extracted from target datasets (not exact copies).
        # Core rules are inserted probabilistically via p_semantic_core and per-rule weights.
        core_applied = False
        if self.rng.random() < self.hp.p_semantic_core and if_budget >= 1:
            nla_rules: List[str] = []
            nla_weights: List[float] = []
            if nla_family and len(state_vars) >= 4 and self.hp.w_core_rel_guard > 0:
                nla_rules.append("rel_guard")
                nla_weights.append(self.hp.w_core_rel_guard)
            if nla_family and len(state_vars) >= 3 and self.hp.w_core_cond_fixed > 0:
                nla_rules.append("cond_fixed")
                nla_weights.append(self.hp.w_core_cond_fixed)
            if (not nla_family) and len(state_vars) >= 3 and self.hp.w_core_linear_state > 0:
                nla_rules.append("linear_state")
                nla_weights.append(self.hp.w_core_linear_state)

            if nla_rules:
                chosen = self.rng.choices(nla_rules, weights=nla_weights, k=1)[0]
            else:
                chosen = ""

            if chosen == "rel_guard":
                # Relational-guard core: A > B*C + D
                x, y, qv, rv = state_vars[0], state_vars[1], state_vars[2], state_vars[3]
                set_init(x, f"({src}%60)+60")
                set_init(y, f"({src}%9)+2")
                set_init(qv, "0")
                set_init(rv, "0")
                guard = f"{x}>{y}*{qv}+{rv}"
                body.append(
                    IfElse(
                        cond=f"{rv}=={y}-1",
                        then_body=[Assign(rv, "0"), Assign(qv, f"{qv}+1")],
                        else_body=[Assign(rv, f"{rv}+1")],
                    )
                )
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "cond_fixed":
                # Conditional update + fixed updates core.
                x, y, z = state_vars[0], state_vars[1], state_vars[2]
                set_init(x, f"({src}%20)+1")
                set_init(y, f"({src}%25)+1")
                set_init(z, "0")
                guard = f"{y}!=0"
                body.append(
                    IfElse(
                        cond=f"{y}%2==1",
                        then_body=[Assign(z, f"{z}+{x}"), Assign(y, f"{y}-1")],
                        else_body=[],
                    )
                )
                body.append(Assign(x, f"2*{x}"))
                body.append(Assign(y, f"{y}/2"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "linear_state":
                # Linear state-machine core.
                t, c, lvar = state_vars[0], state_vars[1], state_vars[2]
                set_init(t, "0")
                set_init(c, "0")
                set_init(lvar, f"({src}%40)+10")
                guard = f"{t}<{lvar}"
                body.append(
                    IfElse(
                        cond=f"{c}!=4",
                        then_body=[Assign(c, f"{c}+1")],
                        else_body=[Assign(c, "1")],
                    )
                )
                body.append(Assign(t, f"{t}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True

        if core_applied:
            append_step = False

        assign_budget = max(0, assign_total - (1 if append_step else 0))
        if used_assign < assign_budget:
            used_assign += self._seed_family_kernel(body, state_vars, ctr, assign_budget - used_assign, nla_family)

        while used_assign < assign_budget:
            rem_assign = assign_budget - used_assign
            can_if = used_if < if_budget and rem_assign >= 1
            can_ifelse = used_if < if_budget and rem_assign >= 2
            choose_if = can_if and (self.rng.random() < 0.40)

            if choose_if:
                aux = self.rng.choice(state_vars)
                cond = self._sample_cond(ctr, lim, aux, vars_pool, nla_family)
                if can_ifelse and self.rng.random() < 0.55:
                    t1 = self.rng.choice(state_vars)
                    p1 = self.rng.choice([w for w in state_vars if w != t1] or [t1])
                    t2 = self.rng.choice(state_vars)
                    p2 = self.rng.choice([w for w in state_vars if w != t2] or [t2])
                    body.append(
                        IfElse(
                            cond=cond,
                            then_body=[self._semantic_assign(t1, p1, ctr, lim, vars_pool, nla_family)],
                            else_body=[self._semantic_assign(t2, p2, ctr, lim, vars_pool, nla_family)],
                        )
                    )
                    used_assign += 2
                    used_if += 1
                else:
                    t = self.rng.choice(state_vars)
                    p = self.rng.choice([w for w in state_vars if w != t] or [t])
                    body.append(IfOnly(cond=cond, then_body=[self._semantic_assign(t, p, ctr, lim, vars_pool, nla_family)]))
                    used_assign += 1
                    used_if += 1
                continue

            t = self.rng.choice(state_vars)
            p = self.rng.choice([w for w in state_vars if w != t] or [t])
            body.append(self._semantic_assign(t, p, ctr, lim, vars_pool, nla_family))
            used_assign += 1

        if append_step:
            body.append(step_stmt)
        return inits, WhileLoop(cond=guard, body=body), [ctr, lim] + state_vars

    def _arrange_loops(self, loops: List[WhileLoop]) -> List[Stmt]:
        if not loops:
            return []

        max_depth = max(1, self.hp.d_max)
        top_level: List[Stmt] = [loops[0]]
        prev_loop = loops[0]
        prev_container: List[Stmt] = top_level
        prev_depth = 1

        for cur in loops[1:]:
            can_nest = prev_depth < max_depth
            do_nest = can_nest and (self.rng.random() < self.hp.q_nest)
            if do_nest:
                prev_loop.body.append(cur)
                cur_container = prev_loop.body
                cur_depth = prev_depth + 1
            else:
                prev_container.append(cur)
                cur_container = prev_container
                cur_depth = prev_depth
            prev_loop = cur
            prev_container = cur_container
            prev_depth = cur_depth

        return top_level

    def sample_program(self, idx: int) -> Program:
        params = self._pick_params()
        alloc = NameAllocator(params=params, rng=self.rng)

        local_inits: List[Tuple[str, str]] = []
        loops: List[WhileLoop] = []
        seen = set()
        universe: List[str] = []

        max_local_vars = max(3, self.hp.m)
        for _ in range(self._sample_loop_count()):
            remaining = max_local_vars - len(seen)
            if remaining < 3:
                break
            inits, loop, produced = self._sample_core_loop(alloc, params, universe, remaining)
            for v, e in inits:
                if v not in seen:
                    local_inits.append((v, e))
                    seen.add(v)
            loops.append(loop)
            universe.extend(produced)

        return Program(name=f"main{idx + 1}", params=params, local_inits=local_inits, body=self._arrange_loops(loops))


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Probabilistic DSL numeric loop synthesis")
    parser.add_argument("--profile", choices=["benchmark", "rich"], default="benchmark")
    parser.add_argument("--out-dir", type=Path, default=Path("generated"), help="Output directory")
    parser.add_argument("--count", type=int, default=50, help="Number of generated C files")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--max-vars", type=int, default=10, help="Maximum number of variables")
    parser.add_argument("--params", type=int, default=3, help="Number of parameter variables")

    parser.add_argument("--top-loops", type=int, default=3, help="Deprecated compatibility alias of --max-loops")
    parser.add_argument("--min-loops", type=int, default=1, help="Program-level while lower bound")
    parser.add_argument("--max-loops", type=int, default=None, help="Program-level while upper bound; actual sampled in [1, max-loops]")
    parser.add_argument("--max-assign", type=int, default=6, help="Per-loop assign upper bound; actual sampled in [1, max-assign], includes loop-step")
    parser.add_argument("--max-ifelse", type=int, default=4, help="Per-loop if/if-else upper bound; actual sampled in [0, max-ifelse]")

    parser.add_argument("--max-depth", type=int, default=2, help="Max loop nesting depth")
    parser.add_argument("--p-multi", type=float, default=0.35, help="Loop continuation probability p")
    parser.add_argument("--q-nest", type=float, default=0.12, help="Loop nesting probability q")

    parser.add_argument("--p-nonlinear", type=float, default=0.58, help="Probability of NLA-like loop family")
    parser.add_argument("--nonlinear-strength", type=float, default=0.70, help="Strength of nonlinear updates in NLA-like loops")
    parser.add_argument("--p-semantic-core", type=float, default=0.50, help="Probability to inject one semantic core rule in a loop")
    parser.add_argument("--w-core-rel-guard", type=float, default=1.0, help="Weight of relational-guard core rule")
    parser.add_argument("--w-core-cond-fixed", type=float, default=1.0, help="Weight of conditional+fixed-update core rule")
    parser.add_argument("--w-core-linear-state", type=float, default=1.0, help="Weight of linear state-machine core rule")
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    max_loops_arg = args.max_loops if args.max_loops is not None else args.top_loops

    hp = HyperParams(
        m=max(4, args.max_vars),
        p=max(1, args.params),
        min_while_fuel=max(1, args.min_loops),
        while_fuel=max(1, max_loops_arg),
        assign_fuel=max(1, args.max_assign),
        ifelse_fuel=max(0, args.max_ifelse),
        d_max=max(1, args.max_depth),
        p_multi=max(0.0, min(1.0, args.p_multi)),
        q_nest=max(0.0, min(1.0, args.q_nest)),
        p_nonlinear=max(0.0, min(1.0, args.p_nonlinear)),
        nonlinear_strength=max(0.0, min(1.0, args.nonlinear_strength)),
        p_semantic_core=max(0.0, min(1.0, args.p_semantic_core)),
        w_core_rel_guard=max(0.0, args.w_core_rel_guard),
        w_core_cond_fixed=max(0.0, args.w_core_cond_fixed),
        w_core_linear_state=max(0.0, args.w_core_linear_state),
    )

    rng = random.Random(args.seed)
    factory = ProbabilisticLoopFactory(hp, rng)

    args.out_dir.mkdir(parents=True, exist_ok=True)
    for i in range(args.count):
        program = factory.sample_program(i)
        out_file = args.out_dir / f"{i + 1}.c"
        out_file.write_text(program.render() + "\n", encoding="utf-8")

    print(f"Generated {args.count} files under {args.out_dir}")


if __name__ == "__main__":
    main()
