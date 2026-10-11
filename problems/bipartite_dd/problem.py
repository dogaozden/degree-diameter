"""The bipartite degree-diameter problem as an evolve Problem plug-in."""
from __future__ import annotations

import tomllib
from pathlib import Path

from evolve.types import Case, CheckerBug

from .checker import check
from .checker_nx import check_nx

PROMPT_HEADER = """You are improving a Python program that builds large bipartite graphs.

Problem: given a maximum degree d and a diameter D, build a bipartite graph with as many vertices as possible such that every vertex has degree at most d and every two vertices are joined by a path of at most D edges. Larger is better. Known records and proven ceilings are shown with the scores.

Your program must define:

    def build(d, D, seed, time_limit):
        ...
        return n, edges   # vertices are 0..n-1, edges is a list of (u, v) pairs

Rules:
- It is called once per case with the case's d and D, an integer seed, and time_limit in seconds. Return before time_limit runs out (leave a margin); slow programs are killed and score 0.
- Allowed imports: the Python standard library, numpy, and `lib` (shown below). No networkx, no files, no network.
- Output must be exactly valid: no duplicate edges, no self-loops, degree <= d, bipartite, diameter <= D. Any violation scores 0 for that case. A good pattern is to construct, then verify with lib.is_valid(n, edges, d, D), and fall back to a smaller valid graph if the check fails.
- Use a single process and a single thread: no multiprocessing, no threads, no subprocesses.
- One program handles every (d, D) case. Specializing by case inside build() is fine."""


class BipartiteDD:
    name = "bipartite_dd"
    harness_dir = Path(__file__).parent           # holds lib.py
    prompt_header = PROMPT_HEADER
    seed_program = harness_dir / "seed.py"

    def __init__(self, cases_path=None):
        path = Path(cases_path) if cases_path else self.harness_dir / "cases.toml"
        with open(path, "rb") as f:
            rows = tomllib.load(f)["case"]
        self.cases = [
            Case(r["id"], {"d": r["d"], "D": r["D"]}, r["record"], r["ceiling"], r["kind"], r["weight"])
            for r in rows
        ]

    def evaluate(self, case, output):
        r = check(output, case.params["d"], case.params["D"])
        if not r.valid:
            return (False, 0.0, r.reason)
        if r.n > case.ceiling:
            raise CheckerBug(f"{case.id}: {r.n} > ceiling {case.ceiling}")
        return (True, float(r.n), "")

    def verify(self, case, output):
        return check_nx(output, case.params["d"], case.params["D"]).valid

    def smoke_case(self):
        return next(c for c in self.cases if c.id == "d3D3")

    def prompt_context(self):
        lib_src = (self.harness_dir / "lib.py").read_text()
        notes = (self.harness_dir / "notes.md").read_text()
        return self.prompt_header + "\n\n## lib.py\n```python\n" + lib_src + "\n```\n\n## Notes\n" + notes


PROBLEM = BipartiteDD()
