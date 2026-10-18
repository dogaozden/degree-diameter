"""C-engine specialist islands: programs keep a Python build() but do the heavy search in C.

Pick one in a config with  problem = "problems.bipartite_dd.islands_c:D7D4"
"""
from pathlib import Path

from .islands import Specialist

PROMPT_HEADER_C = """You are improving a program that builds large bipartite graphs.

Problem: given a maximum degree d and a diameter D, build a bipartite graph with as many vertices as possible such that every vertex has degree at most d and every two vertices are joined by a path of at most D edges. Larger is better. Known records and proven ceilings are shown with the scores.

The program is ONE Python file with two parts:
1. C_SOURCE: a C11 search engine, stored as a raw string. lib.run_c compiles it with `cc -O2 -std=c11 ... -lm` (cached) and runs it as `prog d D seed time_limit`. It reads an optional start graph on stdin ("n m" then m lines "u v", or "0 0") and must print the best valid graph it found, in the same format, before time_limit seconds.
2. def build(d, D, seed, time_limit): Python that builds the best start graph it can with lib (projective planes, lib.araujo_lopez_graph, lifts, its own constructions), runs the C engine via lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=start, timeout=...), parses the result with lib.parse_graph_text, checks it with lib.is_valid, and returns the best valid graph as (n, edges).

Rules:
- Put new search ideas into the C code: it runs 10-100x faster than Python, and the time limit is per case. Python is for constructions and glue.
- C: one file, C11, only standard headers (stdio, stdlib, string, stdint, math, time), no threads, no files, no network, under about 2500 lines. If it fails to compile, the program crashes and you will see the compiler error.
- Python: imports limited to the standard library, numpy and lib; no threads or processes besides the one C run through lib.run_c.
- build() is called once per case with the case's d and D, an integer seed and time_limit in seconds. Return before time_limit runs out; slow programs are killed and score 0.
- Output must be exactly valid: no duplicate edges, no self-loops, degree <= d, bipartite, diameter <= D. Any violation scores 0 for that case. Always check with lib.is_valid and keep a valid fallback.
- The strongest pattern so far: build the best known graph (or the best your search finds), then let C search for a valid graph with MORE vertices starting from it."""


class CSpecialist(Specialist):
    prompt_header = PROMPT_HEADER_C
    seed_program = Path(__file__).parent / "seed_c.py"


D4D5 = CSpecialist(["d4D5"])
D5D5 = CSpecialist(["d5D5"])
D6D5 = CSpecialist(["d6D5"])
D7D5 = CSpecialist(["d7D5"])
D7D4 = CSpecialist(["d7D4"])
D11D4 = CSpecialist(["d11D4"])
D3FAM = CSpecialist(["d11D3", "d13D3", "d15D3"])
D16D3 = CSpecialist(["d16D3"])
D8D5 = CSpecialist(["d8D5"])
D9D5 = CSpecialist(["d9D5"])
D10D5 = CSpecialist(["d10D5"])
D11D5 = CSpecialist(["d11D5"])
D4D7 = CSpecialist(["d4D7"])
D4D8 = CSpecialist(["d4D8"])
D5D7 = CSpecialist(["d5D7"])
D3D9 = CSpecialist(["d3D9"])
D4D9 = CSpecialist(["d4D9"])
