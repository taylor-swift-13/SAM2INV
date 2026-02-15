#!/usr/bin/env python3
from __future__ import annotations

import argparse
import random
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


@dataclass(frozen=True)
class HyperParams:
    m: int = 8
    p: int = 3
    n: int = 3
    k: int = 4
    d_max: int = 2
    p_multi: float = 0.35
    q_nest: float = 0.12


class Stmt:
    def render(self, indent: int = 0) -> List[str]:
        raise NotImplementedError


@dataclass(frozen=True)
class Assign(Stmt):
    target: str
    expr: str

    def render(self, indent: int = 0) -> List[str]:
        pad = " " * indent
        return [f"{pad}{self.target} = {self.expr};"]


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
        if self.else_body:
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
            decl = ", ".join(v for v, _ in self.local_inits)
            lines.append(f"  int {decl};")
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
    def __init__(self, params: Sequence[str], locals_hint: Sequence[str]):
        self.params = set(params)
        self.locals_hint = list(locals_hint)
        self.used = set(params)

    def alloc(self, preferred: str) -> str:
        if preferred not in self.used:
            self.used.add(preferred)
            return preferred
        i = 1
        while f"{preferred}{i}" in self.used:
            i += 1
        name = f"{preferred}{i}"
        self.used.add(name)
        return name

    def alloc_many(self, preferreds: Sequence[str]) -> List[str]:
        return [self.alloc(p) for p in preferreds]


class ProbabilisticLoopFactory:
    def __init__(self, hp: HyperParams, rng: random.Random):
        self.hp = hp
        self.rng = rng
        self.param_candidates = ["a", "b", "k", "n", "m", "p", "q"]

    def _pick_params(self) -> List[str]:
        p = max(1, min(self.hp.p, len(self.param_candidates)))
        return sorted(self.rng.sample(self.param_candidates, k=p))

    def _bound_setup(self, params: Sequence[str], alloc: NameAllocator) -> Tuple[List[Tuple[str, str]], str]:
        src = self.rng.choice(list(params)) if params else "10"
        bound = alloc.alloc("bound")
        modv = self.rng.randint(8, 24)
        inits = [(bound, src if src == "10" else f"{src}")]
        # Keep loop condition simple: while(i < bound)
        # Normalize bound once in statements before loops.
        return inits, bound, modv

    def _template_cubic_progression(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with NLA_lipus/1.c
        a = self.rng.choice(list(params))
        c = alloc.alloc("c")
        x, y, z = alloc.alloc_many(["x", "y", "z"])

        inits = [(c, "0"), (x, "0"), (y, "1"), (z, "6")]
        loop = WhileLoop(
            cond=f"{c}<={a}",
            body=[
                Assign(c, f"{c}+1"),
                Assign(x, f"{x}+{y}"),
                Assign(y, f"{y}+{z}"),
                Assign(z, f"{z}+6"),
            ],
        )
        return inits, [loop]

    def _template_geometric(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with NLA_lipus/9.c
        z = self.rng.choice(list(params))
        k = self.rng.choice([p for p in params if p != z]) if len(params) > 1 else z
        x, y, c = alloc.alloc_many(["x", "y", "c"])
        inits = [(x, "1"), (y, z), (c, "1")]
        loop = WhileLoop(
            cond=f"{c}<{k}",
            body=[
                Assign(c, f"{c}+1"),
                Assign(x, f"{x}*{z}+1"),
                Assign(y, f"{y}*{z}"),
            ],
        )
        return inits, [loop]

    def _template_square_accum(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style close to NLA_lipus/29.c (counted accumulation)
        x = self.rng.choice(list(params))
        y = self.rng.choice([p for p in params if p != x]) if len(params) > 1 else x
        n = self.rng.choice([p for p in params if p not in {x, y}]) if len(params) > 2 else x
        z, w, p = alloc.alloc_many(["z", "w", "p"])
        inits = [(z, "0"), (w, "0"), (p, "0")]
        loop = WhileLoop(
            cond=f"{n}>0",
            body=[
                Assign(z, f"{z}+{x}*{x}"),
                Assign(w, f"{w}+{y}*{y}"),
                Assign(p, f"{p}+{x}*{y}"),
                Assign(n, f"{n}-1"),
            ],
        )
        return inits, [loop]

    def _template_power_sum(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with NLA_lipus/15-19.c
        k = self.rng.choice(list(params))
        y, x, c = alloc.alloc_many(["y", "x", "c"])
        deg = self.rng.choice([1, 2, 3, 4, 5])
        term = y if deg == 1 else "*".join([y] * deg)
        inits = [(y, "0"), (x, "0"), (c, "0")]
        loop = WhileLoop(
            cond=f"{c}<{k}",
            body=[
                Assign(c, f"{c}+1"),
                Assign(y, f"{y}+1"),
                Assign(x, f"{term}+{x}"),
            ],
        )
        return inits, [loop]

    def _template_div_mod_counter(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with NLA_lipus/2.c and /12.c
        x = self.rng.choice(list(params))
        y = self.rng.choice([p for p in params if p != x]) if len(params) > 1 else x
        q, r = alloc.alloc_many(["q", "r"])
        inits = [(q, "0"), (r, "0")]
        loop = WhileLoop(
            cond=f"{x}>{y}*{q}+{r}",
            body=[
                IfElse(
                    cond=f"{r}=={y}-1",
                    then_body=[Assign(r, "0"), Assign(q, f"{q}+1")],
                    else_body=[Assign(r, f"{r}+1")],
                ),
            ],
        )
        return inits, [loop]

    def _template_binary_mul(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with NLA_lipus/14.c (if inside while)
        a = self.rng.choice(list(params))
        b = self.rng.choice([p for p in params if p != a]) if len(params) > 1 else a
        x, y, z = alloc.alloc_many(["x", "y", "z"])
        inits = [(x, a), (y, b), (z, "0")]
        loop = WhileLoop(
            cond=f"{y}!=0",
            body=[
                IfElse(
                    cond=f"{y}%2==1",
                    then_body=[Assign(z, f"{z}+{x}"), Assign(y, f"{y}-1")],
                    else_body=[],
                ),
                Assign(x, f"2*{x}"),
                Assign(y, f"{y}/2"),
            ],
        )
        return inits, [loop]

    def _template_linear_pair_shift(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with SESpec linear family.
        x = self.rng.choice(list(params))
        y = self.rng.choice([p for p in params if p != x]) if len(params) > 1 else x
        step = self.rng.randint(1, 10)
        c = alloc.alloc("c")
        inits = [(c, "0")]
        loop = WhileLoop(
            cond=f"{c}<{self.rng.randint(1, 20)}",
            body=[
                Assign(x, f"{x}+{step}"),
                Assign(y, f"{y}+{step}"),
                Assign(c, f"{c}+1"),
            ],
        )
        return inits, [loop]

    def _template_linear_decrease_to_zero(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with SESpec linear decrement loops.
        n = self.rng.choice(list(params))
        x = alloc.alloc("x")
        inits = [(x, n)]
        loop = WhileLoop(
            cond=f"{x}>0",
            body=[Assign(x, f"{x}-1")],
        )
        return inits, [loop]

    def _template_mod_bucket_count(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Style aligned with SESpec/linear/310.c
        n = self.rng.choice(list(params))
        l, i, j, k, v4, v3, v2 = alloc.alloc_many(["l", "i", "j", "k", "v4", "v3", "v2"])
        inits = [(l, "0"), (i, "0"), (j, "0"), (k, "0"), (v4, "0"), (v3, "0"), (v2, "0")]
        loop = WhileLoop(
            cond=f"{l}<{n}",
            body=[
                IfElse(
                    cond=f"({l}%6)==0",
                    then_body=[Assign(v2, f"{v2}+1")],
                    else_body=[
                        IfElse(
                            cond=f"({l}%5)==0",
                            then_body=[Assign(v3, f"{v3}+1")],
                            else_body=[
                                IfElse(
                                    cond=f"({l}%4)==0",
                                    then_body=[Assign(v4, f"{v4}+1")],
                                    else_body=[
                                        IfElse(
                                            cond=f"({l}%3)==0",
                                            then_body=[Assign(i, f"{i}+1")],
                                            else_body=[
                                                IfElse(
                                                    cond=f"({l}%2)==0",
                                                    then_body=[Assign(j, f"{j}+1")],
                                                    else_body=[Assign(k, f"{k}+1")],
                                                )
                                            ],
                                        )
                                    ],
                                )
                            ],
                        )
                    ],
                ),
                Assign(l, f"{l}+1"),
            ],
        )
        return inits, [loop]

    def _template_gcd_subtractive(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Euclidean-style numeric loop.
        a = self.rng.choice(list(params))
        b = self.rng.choice([p for p in params if p != a]) if len(params) > 1 else a
        x, y = alloc.alloc_many(["x", "y"])
        inits = [(x, a), (y, b)]
        loop = WhileLoop(
            cond=f"{x}!=0&&{y}!=0",
            body=[
                IfElse(
                    cond=f"{x}>{y}",
                    then_body=[Assign(x, f"{x}-{y}")],
                    else_body=[Assign(y, f"{y}-{x}")],
                )
            ],
        )
        return inits, [loop]

    def _template_nested_triangular(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        # Explicit nested loops for DSL extensibility.
        n = self.rng.choice(list(params))
        i, j, s = alloc.alloc_many(["i", "j", "s"])
        inits = [(i, "0"), (j, "0"), (s, "0")]
        inner = WhileLoop(
            cond=f"{j}<{i}",
            body=[
                Assign(s, f"{s}+{j}"),
                Assign(j, f"{j}+1"),
            ],
        )
        outer = WhileLoop(
            cond=f"{i}<{n}",
            body=[
                Assign(j, "0"),
                inner,
                Assign(i, f"{i}+1"),
            ],
        )
        return inits, [outer]

    def _template_nested_affine(self, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        n = self.rng.choice(list(params))
        m = self.rng.choice([p for p in params if p != n]) if len(params) > 1 else n
        i, j, x, y = alloc.alloc_many(["i", "j", "x", "y"])
        inits = [(i, "0"), (j, "0"), (x, "0"), (y, "1")]
        inner = WhileLoop(
            cond=f"{j}<{m}",
            body=[
                Assign(x, f"{x}+{y}"),
                Assign(y, f"{y}+1"),
                Assign(j, f"{j}+1"),
            ],
        )
        outer = WhileLoop(
            cond=f"{i}<{n}",
            body=[
                Assign(j, "0"),
                inner,
                Assign(i, f"{i}+1"),
            ],
        )
        return inits, [outer]

    def _sample_loop_count(self) -> int:
        # Geometric-style continuation:
        # P(L >= 2) = p_multi, P(L >= 3) = p_multi^2
        # capped by n.
        if self.hp.d_max <= 1:
            return 1
        count = 1
        while count < max(1, self.hp.n) and self.rng.random() < self.hp.p_multi:
            count += 1
        return count

    def _choose_templates(self, count: int) -> List[str]:
        base = [
            "cubic_progression",
            "geometric",
            "square_accum",
            "power_sum",
            "div_mod_counter",
            "binary_mul",
            "linear_pair_shift",
            "linear_decrease_to_zero",
            "mod_bucket_count",
            "gcd_subtractive",
        ]
        return [self.rng.choice(base) for _ in range(max(1, count))]

    def _build_from_template(self, name: str, alloc: NameAllocator, params: Sequence[str]) -> Tuple[List[Tuple[str, str]], List[Stmt]]:
        if name == "cubic_progression":
            return self._template_cubic_progression(alloc, params)
        if name == "geometric":
            return self._template_geometric(alloc, params)
        if name == "square_accum":
            return self._template_square_accum(alloc, params)
        if name == "power_sum":
            return self._template_power_sum(alloc, params)
        if name == "div_mod_counter":
            return self._template_div_mod_counter(alloc, params)
        if name == "binary_mul":
            return self._template_binary_mul(alloc, params)
        if name == "linear_pair_shift":
            return self._template_linear_pair_shift(alloc, params)
        if name == "linear_decrease_to_zero":
            return self._template_linear_decrease_to_zero(alloc, params)
        if name == "mod_bucket_count":
            return self._template_mod_bucket_count(alloc, params)
        if name == "gcd_subtractive":
            return self._template_gcd_subtractive(alloc, params)
        if name == "nested_triangular":
            return self._template_nested_triangular(alloc, params)
        if name == "nested_affine":
            return self._template_nested_affine(alloc, params)
        raise ValueError(f"Unknown template: {name}")

    def _arrange_loops(self, loops: List[WhileLoop]) -> List[Stmt]:
        # Rule:
        # - with probability q_nest: current loop nests in previous loop
        # - with probability 1-q: current loop is sequential right after previous loop
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
        alloc = NameAllocator(params=params, locals_hint=[])

        local_inits: List[Tuple[str, str]] = []
        loops: List[WhileLoop] = []
        seen = set()

        loop_count = self._sample_loop_count()
        for tpl in self._choose_templates(loop_count):
            inits, stmts = self._build_from_template(tpl, alloc, params)
            for v, e in inits:
                if v in params:
                    continue
                if v not in seen:
                    local_inits.append((v, e))
                    seen.add(v)
            for s in stmts:
                if isinstance(s, WhileLoop):
                    loops.append(s)

        # Loop tree under function block root:
        # - P(L>=2)=p_multi, P(L>=3)=p_multi^2, ...
        # - with prob q_nest nest in previous loop, else sequential after previous.
        body: List[Stmt] = self._arrange_loops(loops)
        return Program(name=f"main{idx + 1}", params=params, local_inits=local_inits, body=body)


def build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="DSL-based numeric loop synthesis aligned with src/input style")
    parser.add_argument("--profile", choices=["benchmark", "rich"], default="benchmark")
    parser.add_argument("--out-dir", type=Path, default=Path("generated"), help="Output directory")
    parser.add_argument("--count", type=int, default=50, help="Number of generated C files")
    parser.add_argument("--seed", type=int, default=42, help="Random seed")
    parser.add_argument("--max-vars", type=int, default=8, help="Maximum number of variables (m)")
    parser.add_argument("--params", type=int, default=3, help="Number of parameter variables (p)")
    parser.add_argument("--top-loops", type=int, default=3, help="Maximum loop count (n), kept for compatibility")
    parser.add_argument("--max-loops", type=int, default=None, help="Explicit maximum loop count")
    parser.add_argument("--max-assign", type=int, default=4, help="Reserved for compatibility")
    parser.add_argument("--max-depth", type=int, default=2, help="Max nesting depth")
    parser.add_argument("--p-multi", type=float, default=0.35, help="Loop continuation probability p")
    parser.add_argument("--q-nest", type=float, default=0.12, help="Nesting probability q (usually smaller than p)")
    return parser


def main() -> None:
    args = build_arg_parser().parse_args()
    max_loops_arg = args.max_loops if args.max_loops is not None else args.top_loops

    if args.profile == "benchmark":
        top_loops = 3 if max_loops_arg == 3 else max_loops_arg
        max_depth = 1 if args.max_depth == 2 else args.max_depth
        p_multi = 0.35 if abs(args.p_multi - 0.35) < 1e-9 else args.p_multi
        q_nest = 0.10 if abs(args.q_nest - 0.12) < 1e-9 else args.q_nest
    else:
        top_loops = max_loops_arg
        max_depth = args.max_depth
        p_multi = args.p_multi
        q_nest = args.q_nest

    hp = HyperParams(
        m=args.max_vars,
        p=args.params,
        n=max(1, top_loops),
        k=args.max_assign,
        d_max=max(1, max_depth),
        p_multi=p_multi,
        q_nest=q_nest,
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
