#!/usr/bin/env python3
from __future__ import annotations

import argparse
import random
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


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
    p_semantic_core: float = 0.20
    p_while_one: float = 0.18
    w_core_rel_guard: float = 1.0
    w_core_cond_fixed: float = 1.0
    w_core_linear_state: float = 1.0
    w_core_min_update: float = 2.0
    w_core_qr_division: float = 2.2
    w_core_euclid_matrix: float = 0.8


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
class Break(Stmt):
    def render(self, indent: int = 0) -> List[str]:
        return [f"{' ' * indent}break;"]


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
        # Do not overfit variable naming to hints (e.g. bound always named `l`).
        # Keep names diverse to avoid bias in synthesized datasets.
        use_hint = (
            hint
            and len(hint) == 1
            and hint in available
            and self.rng.random() < 0.35
        )
        if use_hint:
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
            # Linear family: forbid '*' and '/' in loop-body updates.
            op = self.rng.choices(["+", "-", "%"], weights=[0.62, 0.34, 0.04], k=1)[0]

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
        # Small chance to deliberately sample a non-progressing loop.
        if self.rng.random() < 0.03:
            dead_guard = self.rng.choice(["1", f"{ctr}>={ctr}", f"{lim}>={lim}"])
            dead_step = Assign(ctr, ctr) if self.rng.random() < 0.6 else Assign(ctr, f"{ctr}+0")
            return [(lim, lim_expr), (ctr, "0")], dead_guard, dead_step

        if self.rng.random() < self.hp.p_while_one:
            start = "0" if self.rng.random() < 0.7 else str(self.rng.randint(1, 3))
            return [(lim, lim_expr), (ctr, start)], "1", Assign(ctr, f"{ctr}+1")

        if nla_family:
            # Mix linear and nonlinear controls for richer guard shapes.
            weights = [0.23, 0.13, 0.11, 0.12, 0.16, 0.11, 0.08, 0.06]
        else:
            # Linear family: disable mul/div loop controls.
            weights = [0.34, 0.16, 0.19, 0.19, 0.0, 0.0, 0.0, 0.12]

        mode = self.rng.choices(
            ["inc1", "dec1", "inc_step", "dec_step", "mul_up", "div_down", "dist_to_limit", "while_one_progress"],
            weights=weights,
            k=1,
        )[0]

        if mode == "inc1":
            start = "0" if self.rng.random() < 0.75 else str(self.rng.randint(1, 4))
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}<={lim}-1", f"{ctr}+1<={lim}"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}+1")

        if mode == "dec1":
            g = self.rng.choice([f"{ctr}>0", f"{ctr}>=1", f"{ctr}-1>=0"])
            return [(lim, lim_expr), (ctr, lim)], g, Assign(ctr, f"{ctr}-1")

        if mode == "inc_step":
            d = self.rng.randint(2, 5)
            start = "0" if self.rng.random() < 0.8 else str(self.rng.randint(1, d))
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}+{d}<={lim}", f"{ctr}<={lim}-{d}"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}+{d}")

        if mode == "dec_step":
            d = self.rng.randint(2, 4)
            g = self.rng.choice([f"{ctr}>{d-1}", f"{ctr}>={d}", f"{ctr}-{d}>=0"])
            return [(lim, lim_expr), (ctr, lim)], g, Assign(ctr, f"{ctr}-{d}")

        if mode == "mul_up":
            mul = self.rng.randint(2, 3)
            g = self.rng.choice([f"{ctr}<{lim}", f"{ctr}*{mul}<={lim}", f"{ctr}<={lim}/{mul}"])
            return [(lim, lim_expr), (ctr, "1")], g, Assign(ctr, f"{ctr}*{mul}")

        if mode == "div_down":
            start = f"{lim}+{self.rng.randint(1, 6)}" if self.rng.random() < 0.5 else lim
            g = self.rng.choice([f"{ctr}>0", f"{ctr}>=1", f"{ctr}>1"])
            return [(lim, lim_expr), (ctr, start)], g, Assign(ctr, f"{ctr}/2")

        if mode == "while_one_progress":
            start = "0" if self.rng.random() < 0.7 else str(self.rng.randint(1, 3))
            return [(lim, lim_expr), (ctr, start)], "1", Assign(ctr, f"{ctr}+1")

        # ctr tracks distance-to-limit; guard references both ctr and lim explicitly.
        d = self.rng.randint(1, 3)
        init = f"{lim}+{self.rng.randint(2, 7)}"
        g = self.rng.choice([f"{ctr}>{lim}", f"{ctr}>={lim}+1", f"{ctr}-{lim}>0"])
        return [(lim, lim_expr), (ctr, init)], g, Assign(ctr, f"{ctr}-{d}")

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

    def _normalize_expr(self, expr: str) -> str:
        return re.sub(r"\s+", "", expr).strip("()")

    def _dedup_loop_body(self, body: List[Stmt], ctr: str) -> List[Stmt]:
        """
        Suppress low-value repetitive updates, e.g. repeated `v=v-v`/`v=v+1` chains.
        Keep control-flow statements unchanged and only trim top-level Assign noise.
        """
        out: List[Stmt] = []
        assign_seen: Dict[Tuple[str, str], int] = {}
        prev_assign_fp: Tuple[str, str] | None = None
        prev_target: str | None = None
        same_target_run = 0

        for st in body:
            if not isinstance(st, Assign):
                out.append(st)
                prev_assign_fp = None
                prev_target = None
                same_target_run = 0
                continue

            tgt = st.target
            expr_n = self._normalize_expr(st.expr)
            fp = (tgt, expr_n)

            if tgt == prev_target:
                same_target_run += 1
            else:
                same_target_run = 1
                prev_target = tgt

            # 1) Drop exact consecutive duplicates.
            if prev_assign_fp == fp:
                continue
            # 2) Keep at most one explicit self-zeroing update like x=x-x.
            if expr_n == f"{tgt}-{tgt}" and assign_seen.get(fp, 0) >= 1:
                continue
            # 3) Cap repeated same assignment forms.
            if assign_seen.get(fp, 0) >= 2:
                continue
            # 4) Avoid long same-target straight-line update chains (except loop counter).
            if tgt != ctr and same_target_run > 2:
                continue

            out.append(st)
            assign_seen[fp] = assign_seen.get(fp, 0) + 1
            prev_assign_fp = fp

        return out

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
        if len(writable) < 2:
            return used

        if nla_family:
            # NLA-like recurrences with generalized semantic motifs:
            # (2) affine chains, (3) multiply-add, (9) scaling pairs.
            a, b = writable[0], writable[1]
            c = writable[2] if len(writable) >= 3 else b
            d = writable[3] if len(writable) >= 4 else a
            mul = self.rng.randint(2, 4)
            off = self.rng.randint(1, 5)
            kernels = [
                [Assign(a, f"{a}+{b}"), Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{self.rng.randint(1, 6)}")],
                [Assign(a, f"{a}*2"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}%{self.rng.randint(2, 9)}")],
                [Assign(a, f"{a}+{ctr}"), Assign(b, f"{b}*{b}"), Assign(c, f"{c}+{a}*{b}")],
                [Assign(a, f"{a}*{mul}+{off}"), Assign(b, f"{b}*{a}+{off}")],
                [Assign(a, f"{a}*{mul}"), Assign(b, f"{b}/{mul}")],
                [Assign(d, f"{d}*{d}+{a}"), Assign(a, f"{a}%{self.rng.randint(2, 9)}")],
            ]
        else:
            # linear-like transitions with generalized semantic motifs:
            # (1) conservation pairs, (2) affine chains, (12) counter decomposition.
            a, b = writable[0], writable[1]
            c = writable[2] if len(writable) >= 3 else b
            d = writable[3] if len(writable) >= 4 else a
            off = self.rng.randint(1, 5)
            kernels = [
                [Assign(a, f"{a}+1"), Assign(b, f"{b}+{a}")],
                [Assign(a, f"{a}+{self.rng.randint(1, 5)}"), Assign(c, f"{c}+{self.rng.randint(1, 4)}")],
                [Assign(b, f"{b}+{c}"), Assign(c, f"{c}+{a}")],
                [Assign(a, f"{a}+1"), Assign(b, f"{b}-1")],
                [Assign(a, f"{a}+{off}"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}+{b}")],
                [Assign(d, f"{a}+{b}+{c}"), Assign(a, f"{a}+1")],
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

        # Allow loops to share existing locals when new-local budget is tight.
        reusable = [v for v in dict.fromkeys(universe) if v not in params]
        use_shared_locals = remaining_local_budget < 3 and len(reusable) >= 3

        if use_shared_locals:
            ctr = self.rng.choice(reusable)
            lim_candidates = [v for v in reusable if v != ctr]
            lim = self.rng.choice(lim_candidates) if lim_candidates else ctr
            state_pool = [v for v in reusable if v not in {ctr, lim}] or [ctr]
            max_state = max(1, min(len(state_pool), 6))
            if nla_family:
                lo = 2 if max_state >= 2 else 1
                state_n = self.rng.randint(lo, max_state)
            else:
                state_n = self.rng.randint(1, max_state)
            state_vars = self.rng.sample(state_pool, k=min(state_n, len(state_pool)))
        else:
            ctr_hint = self.rng.choice(["i", "j", "k", "t", "u", "v"])
            lim_hint = self.rng.choice(["l", "h", "n", "m", "r", "b"])
            ctr = alloc.alloc(ctr_hint)
            lim = alloc.alloc(lim_hint)
            # Reserve 2 locals for loop control (ctr/lim), others for state vars.
            state_cap = max(1, remaining_local_budget - 2)
            state_vars = self._sample_state_vars(alloc, nla_family, state_cap)

        ctrl_inits, guard, step_stmt = self._sample_loop_control(src, ctr, lim, nla_family)
        init_pool = universe + list(params) + [ctr, lim]

        inits: List[Tuple[str, str]] = []
        if not use_shared_locals:
            inits.extend(ctrl_inits)
        for sv in state_vars:
            if not use_shared_locals or sv not in reusable:
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
        # Covers additional semantic motifs:
        # 1) linear conservation, 2) affine chain, 3) multiply-add,
        # 4) remainder buckets, 5) quotient-remainder coupling,
        # 6) monotone-bound update, 7) phase switching,
        # 8) saturation/truncation, 9) scaling pair,
        # 10) two-var compare driven, 11) branch + fixed updates,
        # 12) counter decomposition.
        core_applied = False
        if self.rng.random() < self.hp.p_semantic_core:
            a = state_vars[0]
            b = state_vars[1] if len(state_vars) > 1 else state_vars[0]
            c = state_vars[2] if len(state_vars) > 2 else state_vars[0]
            d = state_vars[3] if len(state_vars) > 3 else state_vars[0]

            candidates: List[str] = []
            weights: List[float] = []

            def allow(name: str, w: float, need_if: int, need_asg: int, need_vars: int) -> None:
                if w > 0 and if_budget >= need_if and assign_total >= need_asg and len(state_vars) >= need_vars:
                    candidates.append(name)
                    weights.append(w)

            # Existing controls reused as coarse weights.
            rel_w = self.hp.w_core_rel_guard
            cond_w = self.hp.w_core_cond_fixed
            lin_w = self.hp.w_core_linear_state
            min_w = self.hp.w_core_min_update
            qr_w = self.hp.w_core_qr_division
            euclid_w = self.hp.w_core_euclid_matrix

            allow("rel_guard", rel_w if nla_family else 0.0, 1, 2, 4)         # (5)
            allow("cond_fixed", cond_w if nla_family else 0.0, 1, 4, 3)       # (11)
            allow("linear_state", lin_w if (not nla_family) else 0.0, 1, 2, 3)  # (10-like FSM)
            allow("conservation", lin_w, 0, 2, 2)                             # (1)
            allow("affine_chain", lin_w + cond_w, 0, 3, 3)                    # (2)
            allow("mul_add", cond_w if nla_family else 0.0, 0, 2, 2)          # (3)
            allow("remainder_buckets", cond_w, 2, 2, 3)                        # (4)
            allow("monotone_bound", lin_w, 1, 1, 2)                            # (6)
            allow("phase_switch", cond_w, 1, 2, 2)                             # (7)
            allow("saturation", cond_w, 1, 1, 2)                               # (8)
            allow("scaling_pair", cond_w if nla_family else 0.0, 0, 2, 2)      # (9): nonlinear-only
            allow("counter_decomp", lin_w, 0, 4, 4)                            # (12)
            allow("gcd_compare", cond_w if nla_family else lin_w, 1, 1, 2)     # (10)

            # Extra linear cores inspired by src/input/linear motifs.
            allow("snapshot_step", lin_w + 0.4 * cond_w, 0, 2, 2)               # m=x; x=x+c
            allow("complement_step", lin_w + 0.5 * cond_w, 0, 2, 2)             # y=n-x; x=x+1
            allow("guarded_snapshot", lin_w + cond_w, 1, 2, 3)                  # if (..) m=x; x=x+1
            allow("triple_decrease", lin_w + cond_w, 2, 3, 3)                   # if(a>0) if(b>0) x-=1,y-=1,z-=1
            allow("stride_progress", lin_w, 0, 1, 1)                            # x=x+2 / x=x+3
            allow("min_update_guarded", min_w, 1, 2, 3)                         # x+=c; if (z<=y) y=z
            allow("min_update_guarded_bound", min_w + 0.6, 1, 2, 3)             # while(x<lim) {x+=1; if(z<=y) y=z;}
            allow("paired_progress", lin_w + 0.4 * cond_w, 0, 2, 2)             # x+=k; y+=k

            # Generic complex paradigms (dataset-agnostic).
            allow("nested_guarded_transitions", lin_w + cond_w, 2, 5, 4)
            allow("piecewise_recurrence", (cond_w + rel_w) if nla_family else 0.0, 2, 6, 5)
            allow("qr_division_step", qr_w, 1, 2, 4)                            # x>y*q+r with q/r updates
            allow("euclid_matrix", euclid_w, 1, 6, 6)                           # coupled Euclid-style updates
            allow("while_one_break_counter", lin_w + cond_w + 0.8, 1, 2, 2)     # explicit while(1) + break
            allow("triple_recurrence_inc", qr_w, 0, 4, 4)                       # n++; x=x+y; y=y+z; z=z+c
            allow("qr_countdown_bucket", qr_w, 1, 3, 4)                         # if(r+1==B){q++;r=0;t--}else{r++;t--}
            allow("mul_affine_pair", cond_w if nla_family else (lin_w + 0.3), 0, 3, 3)  # x=x*z+c; y=y*z; c++
            allow("qr_countdown_split", qr_w, 1, 3, 4)                          # if(r+1==B){q++;r=0}else{r++}; t--
            # Body-first cores requested by user (not bound to while(1)).
            allow("guarded_min_step", min_w + 0.8, 1, 2, 3)                     # if(z<=y) y=z; x=x+1
            allow("mul_pair_progress", (cond_w + 0.4) if nla_family else cond_w, 0, 3, 3)  # x=x*z+c; y=y*z; c++
            allow("triple_recurrence_step", qr_w + 0.5, 0, 4, 4)                # x=x+y; y=y+z; z=z+const; n++
            allow("simple_accumulate", lin_w + 0.7, 0, 1, 2)                    # y+=x
            allow("triangular_progress", lin_w + 0.8, 0, 2, 3)                  # i++; j+=i
            allow("mul_affine_param_pair", (cond_w + 0.8) if nla_family else (lin_w + 0.6), 0, 3, 4)  # c++; x=x*z+a; y=y*z
            allow("power_accumulate", cond_w if nla_family else (lin_w + 0.5), 0, 2, 3)  # y++; x+=y^k
            # while(1)-specific cores (all unique by body shape + break condition).
            allow("while_one_min_break", min_w + 1.0, 2, 3, 3)                  # break on ctr>=lim; min-update + ctr++
            allow("while_one_qr_break", qr_w + 1.0, 2, 3, 4)                    # break on x<=y*q+r; qr step
            allow("while_one_mul_break", cond_w + 1.0, 1, 4, 4)                 # break on c>=lim; mul-affine pair
            allow("while_one_recurrence_break", qr_w + 0.9, 1, 5, 4)            # break on n>lim; 3-var recurrence

            chosen = self.rng.choices(candidates, weights=weights, k=1)[0] if candidates else ""

            if chosen == "rel_guard":
                # (5) x = y*q + r style relation with q/r updates.
                set_init(a, f"({src}%60)+60")
                set_init(b, f"({src}%9)+2")
                set_init(c, "0")
                set_init(d, "0")
                guard = f"{a}>{b}*{c}+{d}"
                body.append(IfElse(cond=f"{d}=={b}-1", then_body=[Assign(d, "0"), Assign(c, f"{c}+1")], else_body=[Assign(d, f"{d}+1")]))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "cond_fixed":
                # (11) branch updates + fixed updates outside branch.
                set_init(a, f"({src}%20)+1")
                set_init(b, f"({src}%25)+1")
                set_init(c, "0")
                guard = f"{b}!=0"
                body.append(IfElse(cond=f"{b}%2==1", then_body=[Assign(c, f"{c}+{a}"), Assign(b, f"{b}-1")], else_body=[]))
                body.append(Assign(a, f"2*{a}"))
                body.append(Assign(b, f"{b}/2"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "linear_state":
                # (10) two-variable compare-driven state transition.
                set_init(a, f"({src}%40)+10")
                set_init(b, f"({src}%30)+6")
                guard = f"{a}!=0&&{b}!=0"
                body.append(IfElse(cond=f"{a}>{b}", then_body=[Assign(a, f"{a}-{b}")], else_body=[Assign(b, f"{b}-{a}")]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "conservation":
                # (1) u-v or u+v style conservation pair.
                if self.rng.random() < 0.5:
                    body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}-1")])
                else:
                    body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}+1")])
                used_assign += 2
                core_applied = True
            elif chosen == "affine_chain":
                # (2) affine recurrence chain.
                body.extend([Assign(a, f"{a}+{self.rng.randint(1,4)}"), Assign(b, f"{b}+{a}"), Assign(c, f"{c}+{b}")])
                used_assign += 3
                core_applied = True
            elif chosen == "mul_add":
                # (3) multiply-add recurrence.
                k = self.rng.randint(2, 4)
                cst = self.rng.randint(1, 5)
                body.extend([Assign(a, f"{a}*{k}+{cst}"), Assign(b, f"{b}*{a}+{cst}")])
                used_assign += 2
                core_applied = True
            elif chosen == "remainder_buckets":
                # (4) remainder bucket counting with 2-way split (generalizable).
                k = self.rng.randint(2, 6)
                r = self.rng.randint(0, k - 1)
                body.append(IfElse(cond=f"{ctr}%{k}=={r}", then_body=[Assign(a, f"{a}+1")], else_body=[Assign(b, f"{b}+1")]))
                # second split to mimic multi-bucket partitions
                body.append(IfElse(cond=f"{ctr}%{k}=={(r+1)%k}", then_body=[Assign(c, f"{c}+1")], else_body=[]))
                used_if += 2
                used_assign += 2
                core_applied = True
            elif chosen == "monotone_bound":
                # (6) monotone variable tied to guard.
                guard = f"{a}<{lim}"
                body.append(IfOnly(cond=f"{a}<{lim}", then_body=[Assign(a, f"{a}+1")]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "phase_switch":
                # (7) phase-dependent update law.
                body.append(
                    IfElse(
                        cond=f"{ctr}<{lim}/2",
                        then_body=[Assign(a, f"{a}+{b}")],
                        else_body=[Assign(a, f"{a}*{b}") if nla_family else Assign(a, f"{a}+1")],
                    )
                )
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "saturation":
                # (8) saturation/truncation via if-else (DSL equivalent).
                cst = self.rng.randint(1, 6)
                body.append(IfElse(cond=f"{a}+{cst}<={lim}", then_body=[Assign(a, f"{a}+{cst}")], else_body=[Assign(a, lim)]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "scaling_pair":
                # (9) scaling pair.
                k = self.rng.randint(2, 4)
                body.extend([Assign(a, f"{a}*{k}"), Assign(b, f"{b}/{k}")])
                used_assign += 2
                core_applied = True
            elif chosen == "counter_decomp":
                # (12) decomposition: c1+c2+c3 tracks step-like progress.
                body.extend([Assign(a, f"{a}+1"), Assign(b, f"{b}+1"), Assign(c, f"{c}+1"), Assign(d, f"{a}+{b}+{c}")])
                used_assign += 4
                core_applied = True
            elif chosen == "gcd_compare":
                # (10) compare-driven dual-variable decrease.
                guard = f"{a}!=0&&{b}!=0"
                body.append(IfElse(cond=f"{a}>{b}", then_body=[Assign(a, f"{a}-{b}")], else_body=[Assign(b, f"{b}-{a}")]))
                used_if += 1
                used_assign += 1
                core_applied = True
            elif chosen == "snapshot_step":
                # linear motif: m=x; x=x+c
                step = self.rng.randint(1, 3)
                body.extend([Assign(b, a), Assign(a, f"{a}+{step}")])
                used_assign += 2
                core_applied = True
            elif chosen == "complement_step":
                # linear motif: y=n-x; x=x+1
                set_init(a, "0")
                body.extend([Assign(b, f"{lim}-{a}"), Assign(a, f"{a}+1")])
                used_assign += 2
                core_applied = True
            elif chosen == "guarded_snapshot":
                # linear motif: if (cond) m=x; x=x+1
                guard_var = c
                body.append(IfOnly(cond=f"{guard_var}<{lim}", then_body=[Assign(b, a)]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "triple_decrease":
                # linear motif: nested guards + synchronized decreases
                set_init(a, f"({src}%20)+5")
                set_init(b, f"({src}%20)+5")
                set_init(c, f"({src}%20)+5")
                guard = f"{a}>0"
                body.append(
                    IfOnly(
                        cond=f"{b}>0",
                        then_body=[
                            IfOnly(cond=f"{c}>0", then_body=[Assign(a, f"{a}-1"), Assign(b, f"{b}-1"), Assign(c, f"{c}-1")])
                        ],
                    )
                )
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "stride_progress":
                # linear motif: x increases by fixed stride > 1
                step = self.rng.randint(2, 4)
                body.append(Assign(a, f"{a}+{step}"))
                used_assign += 1
                core_applied = True
            elif chosen == "min_update_guarded":
                # Linear motif aligned with y=min(y,z)-style guarded update.
                step = self.rng.randint(1, 3)
                body.append(Assign(a, f"{a}+{step}"))
                body.append(IfOnly(cond=f"{c}<={b}", then_body=[Assign(b, c)]))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "min_update_guarded_bound":
                # Strong linear target: bounded progress + guarded min-update.
                set_init(a, "0")
                guard = f"{a}<{lim}"
                body.append(Assign(a, f"{a}+1"))
                body.append(IfOnly(cond=f"{d}<={c}", then_body=[Assign(c, d)]))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "paired_progress":
                # Two-variable synchronized progress often seen in linear set.
                k = self.rng.randint(1, 10)
                body.append(Assign(a, f"{a}+{k}"))
                body.append(Assign(b, f"{b}+{k}"))
                used_assign += 2
                core_applied = True
            elif chosen == "qr_division_step":
                # Quotient-remainder coupling: x > y*q+r.
                set_init(a, f"({src}%60)+60")
                set_init(b, f"({src}%9)+2")
                set_init(c, "0")
                set_init(d, "0")
                guard = f"{a}>{b}*{c}+{d}"
                body.append(
                    IfElse(
                        cond=f"{d}=={b}-1",
                        then_body=[Assign(d, "0"), Assign(c, f"{c}+1")],
                        else_body=[Assign(d, f"{d}+1")],
                    )
                )
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "euclid_matrix":
                # Euclid-style pair reduction with coupled matrix-like updates.
                e = state_vars[4] if len(state_vars) > 4 else a
                f = state_vars[5] if len(state_vars) > 5 else b
                set_init(a, f"({src}%35)+15")
                set_init(b, f"({src}%35)+15")
                set_init(c, "1")
                set_init(d, "0")
                set_init(e, "0")
                set_init(f, "1")
                guard = f"{a}!={b}"
                body.append(
                    IfElse(
                        cond=f"{a}>{b}",
                        then_body=[Assign(a, f"{a}-{b}"), Assign(c, f"{c}-{d}"), Assign(e, f"{e}-{f}")],
                        else_body=[Assign(b, f"{b}-{a}"), Assign(d, f"{d}-{c}"), Assign(f, f"{f}-{e}")],
                    )
                )
                used_if += 1
                used_assign += 6
                core_applied = True
            elif chosen == "while_one_break_counter":
                # Canonical while(1) pattern with explicit break condition.
                guard = "1"
                body.append(IfOnly(cond=f"{ctr}>={lim}", then_body=[Break()]))
                body.append(Assign(a, f"{a}+{self.rng.randint(1, 3)}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "triple_recurrence_inc":
                # n<=a; n++; x=x+y; y=y+z; z=z+c pattern.
                set_init(a, "0")
                set_init(b, "1")
                set_init(c, "6")
                set_init(d, "0")
                guard = f"{d}<={lim}"
                body.append(Assign(d, f"{d}+1"))
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{self.rng.choice([2,4,6])}"))
                used_assign += 4
                core_applied = True
            elif chosen == "qr_countdown_bucket":
                # while(t!=0){ if(r+1==B){q++;r=0;t--} else {r++;t--} }
                set_init(a, "0")  # q
                set_init(b, "0")  # r
                set_init(c, f"({src}%50)+20")  # t
                set_init(d, f"({src}%8)+2")    # B
                guard = f"{c}!=0"
                body.append(
                    IfElse(
                        cond=f"{b}+1=={d}",
                        then_body=[Assign(a, f"{a}+1"), Assign(b, "0"), Assign(c, f"{c}-1")],
                        else_body=[Assign(b, f"{b}+1"), Assign(c, f"{c}-1")],
                    )
                )
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "mul_affine_pair":
                # while(c<k){ c++; x=x*z+cst; y=y*z; }
                set_init(c, "0")
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = f"{c}<{lim}"
                const_term = self.rng.randint(1, 4)
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(a, f"{a}*{zvar}+{const_term}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                used_assign += 3
                core_applied = True
            elif chosen == "qr_countdown_split":
                # while(t!=0){ if(r+1==B){q++;r=0}else{r++}; t--; }
                set_init(a, "0")  # q
                set_init(b, "0")  # r
                set_init(c, f"({src}%40)+10")  # t
                set_init(d, f"({src}%7)+2")    # B
                guard = f"{c}!=0"
                body.append(
                    IfElse(
                        cond=f"{b}+1=={d}",
                        then_body=[Assign(a, f"{a}+1"), Assign(b, "0")],
                        else_body=[Assign(b, f"{b}+1")],
                    )
                )
                body.append(Assign(c, f"{c}-1"))
                used_if += 1
                used_assign += 3
                core_applied = True
            elif chosen == "guarded_min_step":
                # if (z<=y) y=z; x=x+1; (condition-agnostic core body)
                body.append(IfOnly(cond=f"{c}<={b}", then_body=[Assign(b, c)]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 1
                used_assign += 2
                core_applied = True
            elif chosen == "mul_pair_progress":
                # x=x*z+c; y=y*z; c++;
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = f"{c}<{lim}"
                body.append(Assign(a, f"{a}*{zvar}+{c}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                body.append(Assign(c, f"{c}+1"))
                used_assign += 3
                core_applied = True
            elif chosen == "triple_recurrence_step":
                # x=x+y; y=y+z; z=z+const; n++;
                k = self.rng.choice([2, 4, 6])
                guard = f"{d}<={lim}"
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{k}"))
                body.append(Assign(d, f"{d}+1"))
                used_assign += 4
                core_applied = True
            elif chosen == "simple_accumulate":
                # y = y + x
                body.append(Assign(b, f"{b}+{a}"))
                used_assign += 1
                core_applied = True
            elif chosen == "triangular_progress":
                # i = i + 1; j = j + i
                body.append(Assign(a, f"{a}+1"))
                body.append(Assign(b, f"{b}+{a}"))
                used_assign += 2
                core_applied = True
            elif chosen == "mul_affine_param_pair":
                # c = c + 1; x = x*z + a; y = y*z
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = f"{c}<{lim}"
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(a, f"{a}*{zvar}+{src}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                used_assign += 3
                core_applied = True
            elif chosen == "power_accumulate":
                # y = y + 1; x = x + y^k (k in [2..5], using repeated mul)
                k = self.rng.randint(2, 5)
                term = "*".join([b] * k)
                body.append(Assign(b, f"{b}+1"))
                body.append(Assign(a, f"{a}+{term}"))
                used_assign += 2
                core_applied = True
            elif chosen == "while_one_min_break":
                # while(1){ if(ctr>=lim) break; if(z<=y) y=z; ctr++; }
                guard = "1"
                body.append(IfOnly(cond=f"{a}>={lim}", then_body=[Break()]))
                body.append(IfOnly(cond=f"{c}<={b}", then_body=[Assign(b, c)]))
                body.append(Assign(a, f"{a}+1"))
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "while_one_qr_break":
                # while(1){ if(x<=y*q+r) break; if(r==y-1){r=0;q++;} else {r++;} }
                set_init(a, f"({src}%60)+60")  # x
                set_init(b, f"({src}%9)+2")    # y
                set_init(c, "0")               # q
                set_init(d, "0")               # r
                guard = "1"
                body.append(IfOnly(cond=f"{a}<={b}*{c}+{d}", then_body=[Break()]))
                body.append(
                    IfElse(
                        cond=f"{d}=={b}-1",
                        then_body=[Assign(d, "0"), Assign(c, f"{c}+1")],
                        else_body=[Assign(d, f"{d}+1")],
                    )
                )
                used_if += 2
                used_assign += 3
                core_applied = True
            elif chosen == "while_one_mul_break":
                # while(1){ if(c>=lim) break; c++; x=x*z+src; y=y*z; }
                zvar = d
                set_init(zvar, f"({src}%6)+2")
                guard = "1"
                body.append(IfOnly(cond=f"{c}>={lim}", then_body=[Break()]))
                body.append(Assign(c, f"{c}+1"))
                body.append(Assign(a, f"{a}*{zvar}+{src}"))
                body.append(Assign(b, f"{b}*{zvar}"))
                used_if += 1
                used_assign += 4
                core_applied = True
            elif chosen == "while_one_recurrence_break":
                # while(1){ if(n>lim) break; x=x+y; y=y+z; z=z+2/4/6; n++; }
                k = self.rng.choice([2, 4, 6])
                guard = "1"
                body.append(IfOnly(cond=f"{d}>{lim}", then_body=[Break()]))
                body.append(Assign(a, f"{a}+{b}"))
                body.append(Assign(b, f"{b}+{c}"))
                body.append(Assign(c, f"{c}+{k}"))
                body.append(Assign(d, f"{d}+1"))
                used_if += 1
                used_assign += 5
                core_applied = True
            elif chosen == "nested_guarded_transitions":
                # Generic nested guarded state transitions:
                # - outer compare guard
                # - nested reset/advance branch
                # - affine accumulator drift
                # - explicit progress update
                x1, x2, x3, x4 = self.rng.sample(state_vars, k=4)
                set_init(x1, str(self.rng.randint(0, 2)))
                set_init(x2, str(self.rng.randint(0, 2)))
                set_init(x3, f"({src}%{self.rng.randint(20, 50)})+{self.rng.randint(1, 6)}")
                set_init(x4, f"({src}%{self.rng.randint(15, 40)})+{self.rng.randint(1, 6)}")
                guard = f"{ctr}<{lim}"
                step1 = self.rng.randint(1, 2)
                step2 = self.rng.randint(1, 2)
                drift = self.rng.choice([f"{x2}-{x1}", f"{x2}+{x1}", f"{x2}+{step1}"])
                body.append(
                    IfElse(
                        cond=f"{x1}>{x3}",
                        then_body=[
                            Assign(x1, f"{x1}+{step1}"),
                            Assign(x2, f"{x2}+{x1}"),
                        ],
                        else_body=[
                            IfElse(
                                cond=f"{x3}=={lim}",
                                then_body=[Assign(x3, str(self.rng.randint(1, 4)))],
                                else_body=[Assign(x3, f"{x3}+{step2}")],
                            )
                        ],
                    )
                )
                body.append(Assign(x4, f"{x4}+{drift}"))
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 5
                core_applied = True
            elif chosen == "piecewise_recurrence":
                # Generic piecewise nonlinear recurrence:
                # - predicate built from linear form over state
                # - branch-dependent affine/nonlinear updates
                # - monotone progress on one control variable
                pool = state_vars[:]
                if len(pool) < 5:
                    pool = (pool * 5)[:5]
                u, v, w, t, extra = self.rng.sample(pool, k=5)

                denom = self.rng.randint(3, 9)
                set_init(u, f"{src}*{src}")
                set_init(v, f"({src}%{denom})+{self.rng.randint(2, 5)}")
                set_init(w, f"{u}%{v}")
                set_init(t, f"{self.rng.randint(2, 5)}*({u}/{v}+1)")
                set_init(extra, f"{u}%({v}-1)")

                guard = f"{ctr}<{lim}&&{w}!=0"
                k1 = self.rng.randint(1, 3)
                k2 = self.rng.randint(1, 3)
                c1 = self.rng.randint(1, 3)
                c2 = self.rng.randint(1, 3)
                body.append(
                    IfElse(
                        cond=f"{k1}*{w}+{t}<{extra}",
                        then_body=[
                            Assign(w, f"{k2}*{w}-{extra}+{t}+{v}+{c1}"),
                            Assign(t, f"{t}+{self.rng.choice([2,4,6])}"),
                            Assign(extra, w),
                        ],
                        else_body=[
                            IfElse(
                                cond=f"{k1}*{w}+{t}<{v}+{extra}+{c2}",
                                then_body=[
                                    Assign(w, f"{k2}*{w}-{extra}+{t}"),
                                    Assign(v, f"{v}+{self.rng.choice([1,2])}"),
                                ],
                                else_body=[
                                    Assign(w, f"{k2}*{w}-{extra}+{t}-{v}-{c2}"),
                                    Assign(t, f"{t}-{self.rng.choice([2,4,6])}"),
                                ],
                            )
                        ],
                    )
                )
                body.append(Assign(ctr, f"{ctr}+1"))
                used_if += 2
                used_assign += 6
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

        body = self._dedup_loop_body(body, ctr)

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
    parser.add_argument("--p-semantic-core", type=float, default=0.20, help="Probability to inject one semantic core rule in a loop")
    parser.add_argument("--p-while-one", type=float, default=0.18, help="Probability to sample while(1) style control")
    parser.add_argument("--w-core-rel-guard", type=float, default=1.0, help="Weight of relational-guard core rule")
    parser.add_argument("--w-core-cond-fixed", type=float, default=1.0, help="Weight of conditional+fixed-update core rule")
    parser.add_argument("--w-core-linear-state", type=float, default=1.0, help="Weight of linear state-machine core rule")
    parser.add_argument("--w-core-min-update", type=float, default=2.0, help="Weight of min-update guarded core rule")
    parser.add_argument("--w-core-qr-division", type=float, default=2.2, help="Weight of quotient-remainder core rule")
    parser.add_argument("--w-core-euclid-matrix", type=float, default=0.8, help="Weight of Euclid matrix-style core rule")
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
        p_while_one=max(0.0, min(1.0, args.p_while_one)),
        w_core_rel_guard=max(0.0, args.w_core_rel_guard),
        w_core_cond_fixed=max(0.0, args.w_core_cond_fixed),
        w_core_linear_state=max(0.0, args.w_core_linear_state),
        w_core_min_update=max(0.0, args.w_core_min_update),
        w_core_qr_division=max(0.0, args.w_core_qr_division),
        w_core_euclid_matrix=max(0.0, args.w_core_euclid_matrix),
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
