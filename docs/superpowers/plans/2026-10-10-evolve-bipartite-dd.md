# Evolve + Bipartite Degree-Diameter Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build a reusable LLM-driven evolutionary program-search engine that runs on the Claude subscription via `claude -p`. Plug in the bipartite degree-diameter problem, then run a pilot on the Mac.

**Architecture:**
- A plain Python loop (`evolve/`) selects parents, asks Haiku (one-shot, one retry) for new programs, runs each program in a sandboxed subprocess on every case, scores the results with a trusted checker, and commits to git.
- The problem lives in a plug-in folder (`problems/bipartite_dd/`) with its own checker, helper library, starter program, cases and hints.
- Engine tests use a toy problem and a fake mutator, so they spend no allowance.

**Tech Stack:** Python 3.14 (repo `.venv`), numpy, networkx (second checker only), pytest, the `claude` CLI 2.1.296 in headless mode, and git with the `gh`-authenticated remote `origin` (private repo `dogaozden/math`, branch `master`).

**Spec:** `docs/superpowers/specs/2026-10-10-evolve-bipartite-dd-design.md`

## Global Constraints

- All Python runs through `.venv/bin/python`. Tests run with `.venv/bin/python -m pytest`.
- Model calls only go through `claude -p` with:
  - `--output-format stream-json --verbose --model claude-haiku-5-5 --setting-sources "" --strict-mcp-config --disable-slash-commands --tools "" --system-prompt=<text>`
  - the prompt on stdin
  - `cwd` = `~/.cache/claude-p-isolated`
  - a child env that drops every `CLAUDE*` / `ANTHROPIC*` variable except `CLAUDE_CONFIG_DIR` and `CLAUDE_CODE_OAUTH_TOKEN`, and sets `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`
- Never `--bare`, never an API key, never a model alias or `--fallback-model`. Refuse to continue if the init event's `apiKeySource` is not `"none"`.
- Stop calling the model once any `rate_limit_event.rate_limit_info.unifiedWindows.*.utilization` reaches `stop_at` (default 0.9), or after a subscription-limit error.
- Candidate programs define `build(**params, seed, time_limit)`. For this problem that is `build(d, D, seed, time_limit)`, returning `(n, edges)` or `{"n": n, "edges": edges}`.
- Candidate ids: `g{gen:03d}-c{idx:02d}`. The seed is `g000-seed`.
- Exit codes for `python -m evolve run`: 0 = finished, 3 = budget stop, 4 = checker bug.
- No network access is needed by candidates. Numeric threads are pinned to 1 in candidate subprocesses.
- Commit after each task with conventional-commit messages ending in:
  ```
  Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
  Claude-Session: https://claude.ai/code/session_01BUMdzXMSdYyesowPZnwehe
  ```
  Implementer subagents commit but do NOT push. The coordinator pushes.

## Review Focus

1. **A candidate that spawns child processes or hangs in C code.** The runner must kill the whole process group at timeout and return `timeout`, not hang. Pinned by `test_timeout_kills_grandchild` in Task 5.
2. **Haiku replies with prose, several code blocks, or a block without the `python` tag.** The extractor takes the last block that defines `build`. Pinned by `test_extract_code_variants` in Task 7.
3. **The run is interrupted mid-generation (Ctrl-C or a crash), then restarted.** No candidate is evaluated twice, no task is generated twice, and the run finishes. Pinned by `test_resume_after_crash` in Task 8.
4. **A graph output with numpy integers, tuples or sets instead of plain lists.** It is serialized and checked fine. Pinned by `test_numpy_output_ok` in Task 5 and `test_parse_accepts_tuple_and_dict` in Task 2.
5. **A disconnected graph or an isolated vertex.** It is rejected as a diameter failure by both checkers. Pinned by `test_disconnected_fails` in Task 2.

---

## File Structure

```text
pyproject.toml                         pytest config (pythonpath = ["."])
evolve/__init__.py
evolve/__main__.py                     -> cli.main()
evolve/types.py                        Case, CaseScore, Problem protocol, CheckerBug, load_problem   (Task 1)
evolve/runner.py, evolve/_harness.py   subprocess execution of one program on one case           (Task 5)
evolve/store.py                        run folder I/O, CandidateRecord                             (Task 6)
evolve/select.py                       fitness, parent pool, role and parent sampling              (Task 6)
evolve/mutator.py                      prompts, claude -p wrapper, FakeMutator, BudgetStop         (Task 7)
evolve/config.py                       RunConfig + load_config                                     (Task 8)
evolve/loop.py                         the generation loop                                         (Task 8)
evolve/cli.py                          `run` and `status` commands                                 (Task 8)
problems/__init__.py
problems/bipartite_dd/__init__.py
problems/bipartite_dd/checker.py       trusted checker                                             (Task 2)
problems/bipartite_dd/checker_nx.py    independent networkx checker                                (Task 2)
problems/bipartite_dd/lib.py           helper library for candidates                               (Task 3)
problems/bipartite_dd/cases.toml       cases                                                       (Task 4)
problems/bipartite_dd/seed.py          starter program                                             (Task 4)
problems/bipartite_dd/notes.md         hints for Haiku                                             (Task 4)
problems/bipartite_dd/problem.py       PROBLEM plug-in object                                      (Task 4)
configs/pilot.toml, configs/smoke.toml                                                             (Task 8)
tests/graphs.py                        shared test graphs (Heawood, Tutte–Coxeter)                 (Task 1)
tests/toy_problem.py                   tiny problem for engine tests                               (Task 1)
tests/test_*.py
```

Execution waves:
- Task 1 runs first.
- Tasks 2, 3, 5, 6 and 7 run in parallel, since they touch disjoint files.
- Tasks 4 and 8 run in parallel after that.
- Tasks 9 and 10 are done by the coordinator.

---

### Task 1: Scaffolding, shared types and test fixtures (coordinator)

**Files:**
- Create: `pyproject.toml`, `evolve/__init__.py`, `evolve/types.py`, `problems/__init__.py`, `problems/bipartite_dd/__init__.py`, `tests/graphs.py`, `tests/toy_problem.py`, `tests/test_types.py`
- Modify: `.gitignore`

**Interfaces — Produces:**

```python
# evolve/types.py
from dataclasses import dataclass, field
from pathlib import Path
from typing import Protocol, Any
import importlib

class CheckerBug(Exception):
    """A checked value exceeded the case's proven ceiling: the checker is wrong. Stops the run."""

@dataclass(frozen=True)
class Case:
    id: str
    params: dict          # passed as build(**params, seed=..., time_limit=...)
    record: float         # best known value (score = value / record)
    ceiling: float        # proven upper bound; value > ceiling => CheckerBug
    kind: str             # "calibration" | "target"
    weight: float

@dataclass(frozen=True)
class CaseScore:
    case_id: str
    status: str           # "ok" | "timeout" | "crash" | "bad_output"
    valid: bool
    value: float          # 0.0 if not valid
    score: float          # value / record, 0.0 if not valid
    reason: str           # "" if valid
    wall_s: float

class Problem(Protocol):
    name: str
    cases: list[Case]
    harness_dir: Path     # put on sys.path for candidates
    seed_program: Path
    def evaluate(self, case: Case, output: Any) -> tuple[bool, float, str]: ...   # (valid, value, reason); may raise CheckerBug
    def verify(self, case: Case, output: Any) -> bool: ...                       # independent second check
    def prompt_context(self) -> str: ...
    def smoke_case(self) -> Case: ...

def load_problem(module_path: str) -> Problem:
    return importlib.import_module(module_path).PROBLEM
```

`tests/graphs.py` provides `lcf(n, jumps) -> tuple[int, list[tuple[int,int]]]`, `HEAWOOD = lcf(14, [5, -5])` (valid for d=3, D=3) and `TUTTE_COXETER = lcf(30, [-13, -9, 7, -7, 9, 13])` (valid for d=3, D=4).

`tests/toy_problem.py` provides `PROBLEM`, a problem with:
- cases `c1` (params `{"x": 3}`, record 6, ceiling 100, calibration, weight 1) and `c2` (params `{"x": 5}`, record 10, ceiling 100, target, weight 2)
- `evaluate(case, output)`: valid iff output is a number, value = float(output); raises `CheckerBug` if value > ceiling
- `verify`: same rule, without raising
- `smoke_case()` = c1
- `harness_dir` = the `tests/toy_lib` folder, which holds `toy_lib/helper.py` with `def double(x): return 2 * x`
- `seed_program` = `tests/toy_lib/seed.py`, with `def build(x, seed, time_limit): return x`

- [x] Steps: write the files, `pip install numpy networkx pytest` into `.venv`, run `pytest tests/test_types.py`, commit, push.

---

### Task 2: Trusted checker and independent networkx checker

**Files:**
- Create: `problems/bipartite_dd/checker.py`, `problems/bipartite_dd/checker_nx.py`
- Test: `tests/test_checker.py`

**Interfaces:**
- Consumes: `tests/graphs.py` (`HEAWOOD`, `TUTTE_COXETER`, `lcf`).
- Produces:
```python
# problems/bipartite_dd/checker.py
from dataclasses import dataclass
@dataclass(frozen=True)
class CheckResult:
    valid: bool
    n: int        # vertex count (0 if malformed)
    reason: str   # "" if valid, else starts with one of:
                  # "malformed", "label out of range", "self-loop", "duplicate edge",
                  # "degree", "not bipartite", "diameter"
MAX_N = 2_000_000
def parse_output(output) -> tuple[int, list[tuple[int, int]]]   # raises ValueError("malformed: ...")
def check(output, d: int, D: int) -> CheckResult

# problems/bipartite_dd/checker_nx.py
from problems.bipartite_dd.checker import CheckResult, parse_output
def check_nx(output, d: int, D: int) -> CheckResult
```

Rules for `parse_output`:
- It accepts `[n, edges]`, `(n, edges)` or `{"n": n, "edges": edges}`.
- `n` must be an `int` (not a `bool`) with `1 <= n <= MAX_N`.
- `edges` must be a list or tuple whose items are length-2 lists or tuples of ints (not bools). Integer-valued floats are rejected.
- It returns `(n, [(u, v), ...])` as plain ints.
- Labels must satisfy `0 <= u, v < n`. A label check failure raises `ValueError("label out of range: ...")`.

`check` order:
1. parse; a `ValueError` message becomes the reason
2. self-loop
3. duplicate (unordered) edge
4. degree `> d` (reason `"degree: vertex 7 has 5 > 4"`)
5. bipartite, by BFS 2-colouring over all components
6. diameter, by bitset reachability

Reference algorithm for the diameter step:
```python
reach = [1 << v for v in range(n)]
for _ in range(D):
    reach = [r | _or_neighbors(reach, adj[v]) for v, r in enumerate(reach)]
full = (1 << n) - 1
bad = next((v for v, r in enumerate(reach) if r != full), None)
# invalid if bad is not None: reason "diameter: vertex {bad} cannot reach all vertices within D"
```
Here `_or_neighbors` ORs `reach[u]` for `u in adj[v]`. Each round must use the previous round's list, not one updated in place.

`check_nx` builds an `nx.Graph`. It checks:
- edge count equals the number of parsed edges (so duplicates fail)
- `nx.number_of_selfloops == 0`
- max degree `<= d`
- `nx.is_bipartite`
- for n > 1: `nx.is_connected` and `nx.diameter(G) <= D`

It reports the same reason prefixes.

- [ ] **Step 1: Write the failing tests** in `tests/test_checker.py`:

```python
import random
import pytest
from problems.bipartite_dd.checker import check, parse_output
from problems.bipartite_dd.checker_nx import check_nx
from tests.graphs import HEAWOOD, TUTTE_COXETER, lcf

BOTH = [check, check_nx]

@pytest.mark.parametrize("fn", BOTH)
def test_heawood_valid(fn):
    r = fn(HEAWOOD, 3, 3)
    assert r.valid and r.n == 14 and r.reason == ""

@pytest.mark.parametrize("fn", BOTH)
def test_tutte_coxeter_valid_d3D4_not_D3(fn):
    assert fn(TUTTE_COXETER, 3, 4).valid
    r = fn(TUTTE_COXETER, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")

@pytest.mark.parametrize("fn", BOTH)
def test_k4_not_bipartite(fn):
    edges = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
    r = fn((4, edges), 3, 3)
    assert not r.valid and r.reason.startswith("not bipartite")

@pytest.mark.parametrize("fn", BOTH)
def test_degree_violation(fn):
    star = (5, [(0,1),(0,2),(0,3),(0,4)])
    r = fn(star, 3, 3)
    assert not r.valid and r.reason.startswith("degree")

@pytest.mark.parametrize("fn", BOTH)
def test_cycle16_too_wide(fn):
    c16 = (16, [(i, (i+1) % 16) for i in range(16)])
    r = fn(c16, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")
    assert fn(c16, 2, 8).valid

@pytest.mark.parametrize("fn", BOTH)
def test_duplicate_and_selfloop(fn):
    assert fn((2, [(0,1),(1,0)]), 3, 3).reason.startswith("duplicate edge")
    assert fn((2, [(0,0),(0,1)]), 3, 3).reason.startswith("self-loop")

@pytest.mark.parametrize("fn", BOTH)
def test_disconnected_fails(fn):
    n, e = HEAWOOD
    two = (2*n, e + [(u+n, v+n) for u, v in e])
    r = fn(two, 3, 3)
    assert not r.valid and r.reason.startswith("diameter")
    isolated = (15, list(e))
    assert fn(isolated, 3, 3).reason.startswith("diameter")

@pytest.mark.parametrize("fn", BOTH)
@pytest.mark.parametrize("bad", ["x", None, [3], (True, []), (3, [(0,)]), (3, [(0, 5)]), (3, [(0, 1.0)]), {"n": 2}, (0, [])])
def test_malformed(fn, bad):
    r = fn(bad, 3, 3)
    assert not r.valid
    assert r.reason.startswith("malformed") or r.reason.startswith("label out of range")

def test_parse_accepts_tuple_and_dict():
    assert parse_output([2, [[0, 1]]]) == (2, [(0, 1)])
    assert parse_output({"n": 2, "edges": [(0, 1)]}) == (2, [(0, 1)])

@pytest.mark.parametrize("fn", BOTH)
def test_single_vertex_valid(fn):
    assert fn((1, []), 3, 3).valid

def test_checkers_agree_on_random_graphs():
    rng = random.Random(7)
    for _ in range(300):
        a = rng.randint(1, 9); b = rng.randint(1, 9); n = a + b
        p = rng.random()
        edges = [(i, a + j) for i in range(a) for j in range(b) if rng.random() < p]
        if rng.random() < 0.2 and n >= 3:
            edges.append((0, 1 if a > 1 else n - 1))  # sometimes break bipartiteness
        edges = list(dict.fromkeys(tuple(sorted(e)) for e in edges if e[0] != e[1]))
        d = rng.randint(1, 6); D = rng.randint(1, 5)
        assert check((n, edges), d, D).valid == check_nx((n, edges), d, D).valid
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_checker.py -q`. Expected: FAIL (import errors).
- [ ] **Step 3:** Implement `checker.py` and `checker_nx.py` per the interface and rules above.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_checker.py -q`. Expected: all pass.
- [ ] **Step 5:** Commit with `git add problems/bipartite_dd/checker.py problems/bipartite_dd/checker_nx.py tests/test_checker.py && git commit -m "feat: trusted and networkx checkers for bipartite degree-diameter"`, plus the trailer from Global Constraints.

---

### Task 3: Helper library for candidates

**Files:**
- Create: `problems/bipartite_dd/lib.py`
- Test: `tests/test_lib.py`

**Interfaces — Produces** (`problems/bipartite_dd/lib.py`). It depends only on the standard library and numpy, with no imports from `checker` or `evolve`, because candidates import it as `import lib`:

```python
def is_prime_power(q: int) -> bool
class GF:
    """Finite field of prime-power order q. Elements are ints 0..q-1 (base-p digits = polynomial coefficients)."""
    def __init__(self, q: int)            # ValueError if q is not a prime power
    q: int; p: int; k: int
    add_table: "np.ndarray"               # shape (q, q), dtype int64
    mul_table: "np.ndarray"
    def add(self, a: int, b: int) -> int
    def sub(self, a: int, b: int) -> int
    def neg(self, a: int) -> int
    def mul(self, a: int, b: int) -> int
    def inv(self, a: int) -> int          # ValueError on 0
    def pow(self, a: int, e: int) -> int
    def primitive_element(self) -> int    # a generator of the multiplicative group

def projective_plane_incidence(q: int) -> tuple[int, list[tuple[int, int]]]
    # m = q*q + q + 1; vertices 0..m-1 = points, m..2m-1 = lines.
    # Points/lines = normalized nonzero vectors of GF(q)^3 (first nonzero coordinate = 1), in a fixed sorted order.
    # Point i is adjacent to line m + j iff dot(point_i, line_j) == 0 in GF(q).
    # Also exposes: projective_points(q) -> list[tuple[int,int,int]] (the same ordering).

def voltage_lift(base_n: int, darts: list[tuple[int, int, int]], m: int) -> tuple[int, list[tuple[int, int]]]
    # Base vertex u, group element g -> lifted vertex u*m + g. Dart (u, v, a) gives the edges
    # (u*m + g) -- (v*m + (g + a) % m) for all g in Z_m. Loops (u == v) are allowed.
    # The result drops self-loops and deduplicates unordered edges. n = base_n * m.

def haar_graph(m: int, S) -> tuple[int, list[tuple[int, int]]]
    # vertices a_i = i, b_i = m + i; edges a_i -- b_{(i + s) % m} for s in sorted(set(x % m for x in S)).

def adjacency(n: int, edges) -> list[list[int]]
def max_degree(n: int, edges) -> int
def is_bipartite(n: int, edges) -> bool
def within_diameter(n: int, edges, D: int) -> bool      # bitset method; False if disconnected
def bad_pairs(n: int, edges, D: int) -> int             # unordered pairs at distance > D (unreachable counts)
def relabel(edges) -> tuple[int, list[tuple[int, int]]] # compact labels 0..n-1 in sorted order of old labels
```

Implementation notes:
- **GF(p^k):** find the lexicographically first monic irreducible polynomial of degree k over Z_p by brute force (test it has no factor of degree ≤ k/2 by trying all monic polynomials of that degree). Precompute `add_table` and `mul_table` with polynomial arithmetic mod that polynomial. Methods index the tables. Allow q ≤ 1024.
- **`bad_pairs`:** run D rounds of reachability as in Task 2, then return `sum(n - r.bit_count() for r in reach) // 2`.

- [ ] **Step 1: Write the failing tests** in `tests/test_lib.py`:

```python
import itertools, random
import networkx as nx
import pytest
from problems.bipartite_dd import lib

def test_is_prime_power():
    assert [q for q in range(1, 30) if lib.is_prime_power(q)] == [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29]

@pytest.mark.parametrize("q", [2,3,4,5,7,8,9,16,25,27])
def test_field_axioms(q):
    F = lib.GF(q)
    els = range(q)
    for a in els:
        assert F.add(a, 0) == a and F.mul(a, 1) == a and F.add(a, F.neg(a)) == 0
        if a: assert F.mul(a, F.inv(a)) == 1
    rng = random.Random(q)
    for _ in range(300):
        a, b, c = (rng.randrange(q) for _ in range(3))
        assert F.mul(a, F.add(b, c)) == F.add(F.mul(a, b), F.mul(a, c))
        assert F.mul(F.mul(a, b), c) == F.mul(a, F.mul(b, c))
        assert F.add(a, b) == F.add(b, a) and F.mul(a, b) == F.mul(b, a)
    g = F.primitive_element()
    assert len({F.pow(g, e) for e in range(q - 1)}) == q - 1

def test_gf_rejects_non_prime_power():
    with pytest.raises(ValueError):
        lib.GF(6)

@pytest.mark.parametrize("q", [2,3,4,5,7,8,9,11])
def test_projective_plane_is_moore_graph(q):
    n, edges = lib.projective_plane_incidence(q)
    m = q*q + q + 1
    assert n == 2*m and len(edges) == (q+1)*m
    assert lib.max_degree(n, edges) == q + 1
    assert lib.is_bipartite(n, edges)
    assert lib.within_diameter(n, edges, 3)
    assert not lib.within_diameter(n, edges, 2)

def test_haar_heawood():
    n, edges = lib.haar_graph(7, [0, 1, 3])
    G = nx.Graph(edges)
    assert n == 14 and nx.is_bipartite(G) and nx.diameter(G) == 3
    assert {d for _, d in G.degree()} == {3}

def test_voltage_lift_matches_haar():
    n, edges = lib.voltage_lift(2, [(0, 1, 0), (0, 1, 1), (0, 1, 3)], 7)
    assert n == 14 and len(edges) == 21 and lib.within_diameter(n, edges, 3)

def test_voltage_lift_loop_dedup():
    n, edges = lib.voltage_lift(1, [(0, 0, 2)], 4)   # 2 == -2 mod 4: only 2 distinct edges
    assert n == 4 and sorted(edges) == [(0, 2), (1, 3)]

def test_within_diameter_matches_networkx():
    rng = random.Random(3)
    for _ in range(200):
        n = rng.randint(1, 12)
        edges = [(u, v) for u, v in itertools.combinations(range(n), 2) if rng.random() < 0.3]
        D = rng.randint(1, 4)
        G = nx.Graph(); G.add_nodes_from(range(n)); G.add_edges_from(edges)
        expect = nx.is_connected(G) and (n == 1 or nx.diameter(G) <= D)
        assert lib.within_diameter(n, edges, D) == expect

def test_bad_pairs_path():
    assert lib.bad_pairs(4, [(0,1),(1,2),(2,3)], 2) == 1
    assert lib.bad_pairs(4, [(0,1),(1,2),(2,3)], 3) == 0
    assert lib.bad_pairs(3, [(0,1)], 5) == 2

def test_relabel():
    assert lib.relabel([(10, 30), (30, 20)]) == (3, [(0, 2), (2, 1)])
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_lib.py -q`. Expected: FAIL.
- [ ] **Step 3:** Implement `lib.py`. Every public function needs a one-line docstring, because Haiku reads this file.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_lib.py -q`. Expected: all pass, in under 30 s.
- [ ] **Step 5:** Commit with `git add problems/bipartite_dd/lib.py tests/test_lib.py && git commit -m "feat: helper library (GF(q), projective planes, lifts, Haar graphs)"`, plus the trailer.

---

### Task 4: Problem plug-in (cases, starter, notes, PROBLEM)

Depends on Tasks 2 and 3.

**Files:**
- Create: `problems/bipartite_dd/cases.toml`, `seed.py`, `notes.md`, `problem.py`
- Test: `tests/test_problem.py`

**Interfaces:**
- Consumes: `evolve.types.Case`, `CheckerBug`; `checker.check`; `checker_nx.check_nx`; `lib.*`.
- Produces: `problems.bipartite_dd.problem.PROBLEM` implementing `evolve.types.Problem`, with `name = "bipartite_dd"`.

`cases.toml` holds one `[[case]]` table per row, with keys `id, d, D, record, ceiling, kind, weight`:

| id | d | D | record | ceiling | kind | weight |
|---|---|---|---|---|---|---|
| d3D3 | 3 | 3 | 14 | 14 | calibration | 1 |
| d4D3 | 4 | 3 | 26 | 26 | calibration | 1 |
| d5D3 | 5 | 3 | 42 | 42 | calibration | 1 |
| d6D3 | 6 | 3 | 62 | 62 | calibration | 1 |
| d3D4 | 3 | 4 | 30 | 30 | calibration | 1 |
| d4D4 | 4 | 4 | 80 | 80 | calibration | 1 |
| d3D5 | 3 | 5 | 56 | 56 | calibration | 1 |
| d7D3 | 7 | 3 | 80 | 80 | calibration | 1 |
| d4D5 | 4 | 5 | 160 | 236 | target | 2 |
| d5D5 | 5 | 5 | 336 | 676 | target | 2 |
| d6D5 | 6 | 5 | 684 | 1556 | target | 2 |
| d7D4 | 7 | 4 | 346 | 518 | target | 2 |
| d11D3 | 11 | 3 | 190 | 220 | target | 2 |

`Case.params = {"d": d, "D": D}`.

`problem.py`:
```python
class BipartiteDD:
    name = "bipartite_dd"
    def __init__(self, cases_path=None): ...      # tomllib; cases in file order
    harness_dir = Path(__file__).parent           # holds lib.py
    seed_program = harness_dir / "seed.py"
    def evaluate(self, case, output):
        r = check(output, case.params["d"], case.params["D"])
        if not r.valid: return (False, 0.0, r.reason)
        if r.n > case.ceiling: raise CheckerBug(f"{case.id}: {r.n} > ceiling {case.ceiling}")
        return (True, float(r.n), "")
    def verify(self, case, output): return check_nx(output, case.params["d"], case.params["D"]).valid
    def smoke_case(self): return the case with id "d3D3"
    def prompt_context(self) -> str: PROMPT_HEADER + "\n\n## lib.py\n```python\n" + lib source + "\n```\n\n## Notes\n" + notes.md text
PROBLEM = BipartiteDD()
```

`PROMPT_HEADER` (verbatim):
```text
You are improving a Python program that builds large bipartite graphs.

Problem: given a maximum degree d and a diameter D, build a bipartite graph with as many vertices as possible such that every vertex has degree at most d and every two vertices are joined by a path of at most D edges. Larger is better. Known records and proven ceilings are shown with the scores.

Your program must define:

    def build(d, D, seed, time_limit):
        ...
        return n, edges   # vertices are 0..n-1, edges is a list of (u, v) pairs

Rules:
- It is called once per case with the case's d and D, an integer seed, and time_limit in seconds. Return before time_limit runs out (leave a margin); slow programs are killed and score 0.
- Allowed imports: the Python standard library, numpy, and `lib` (shown below). No networkx, no files, no network.
- Output must be exactly valid: no duplicate edges, no self-loops, degree <= d, bipartite, diameter <= D. Any violation scores 0 for that case. A good pattern is to construct, then verify with lib.within_diameter / lib.max_degree / lib.is_bipartite, and fall back to a smaller valid graph if the check fails.
- One program handles every (d, D) case. Specializing by case inside build() is fine.
```

`seed.py` (starter, verbatim):
```python
import random
import time
import lib

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
```

`notes.md` (verbatim):
```markdown
# Construction ideas that have produced records

- Moore bound: a bipartite graph with max degree d and diameter D has at most 2((d-1)^D - 1)/(d-2) vertices. Records approach it only through structure.
- D = 3: if d-1 is a prime power, the incidence graph of the projective plane PG(2, d-1) meets the bound (lib.projective_plane_incidence). Otherwise start from PG(2, q) with q the largest prime power below d-1, then add vertices and edges using the spare degree. Araujo-Pardo and López got order 2(q^2+q+5), degree q+2, by adding 8 vertices to PG(2,q).
- Voltage lifts: pick a small base multigraph (a few vertices, loops and parallel edges allowed) and a cyclic group Z_m. Give each edge a voltage. The lift (lib.voltage_lift) has base_n * m vertices and inherits degree. Many records come from lifts with 2-6 base vertices, found by searching voltages. Search m and voltages, then keep the largest lift that passes lib.within_diameter.
- Haar graphs (lib.haar_graph) are the simplest lifts: base = two vertices joined by d parallel edges. They are bipartite automatically.
- Generalized polygons give the optimal graphs for D = 4 (generalized quadrangles, 2(q+1)(q^2+1) vertices for d = q+1) and D = 6 (generalized hexagons). The incidence graph of points and lines of the quadrangle W(q) is a good start for D = 4.
- Duplication (Delorme-Farhi): replace each vertex of a good graph by k copies and connect copies with a structured pattern. This multiplies the order while increasing the degree.
- Repair search: start from a large near-valid graph, then remove the vertices involved in the most bad pairs (lib.bad_pairs counts them) or rewire edges until it is valid.
- Bipartiteness comes free if every edge joins an "A" vertex to a "B" vertex: build A and B parts explicitly.
```

- [ ] **Step 1: Write the failing tests** in `tests/test_problem.py`:

```python
import pytest
from evolve.types import CheckerBug, Case
from problems.bipartite_dd.problem import PROBLEM
from tests.graphs import HEAWOOD

def test_cases_loaded():
    ids = [c.id for c in PROBLEM.cases]
    assert ids[:3] == ["d3D3", "d4D3", "d5D3"] and len(ids) == 13
    c = {c.id: c for c in PROBLEM.cases}
    assert c["d4D5"].record == 160 and c["d4D5"].ceiling == 236 and c["d4D5"].kind == "target" and c["d4D5"].weight == 2
    assert c["d7D3"].params == {"d": 7, "D": 3}

def test_evaluate_and_verify():
    c = PROBLEM.smoke_case()
    assert c.id == "d3D3"
    assert PROBLEM.evaluate(c, HEAWOOD) == (True, 14.0, "")
    assert PROBLEM.verify(c, HEAWOOD)
    ok, value, reason = PROBLEM.evaluate(c, (3, [(0, 1), (1, 2), (2, 0)]))
    assert not ok and value == 0.0 and reason.startswith("not bipartite")

def test_ceiling_breach_raises():
    low = Case("x", {"d": 3, "D": 3}, record=10, ceiling=10, kind="target", weight=1)
    with pytest.raises(CheckerBug):
        PROBLEM.evaluate(low, HEAWOOD)

def test_prompt_context_mentions_interface_and_lib():
    t = PROBLEM.prompt_context()
    assert "def build(d, D, seed, time_limit)" in t and "def voltage_lift" in t and "Voltage lifts" in t

def test_seed_valid_everywhere_and_optimal_on_planes():
    import importlib.util, sys
    sys.path.insert(0, str(PROBLEM.harness_dir))
    spec = importlib.util.spec_from_file_location("seed_mod", PROBLEM.seed_program)
    mod = importlib.util.module_from_spec(spec); spec.loader.exec_module(mod)
    for c in PROBLEM.cases:
        out = mod.build(**c.params, seed=0, time_limit=2.0)
        ok, value, reason = PROBLEM.evaluate(c, out)
        assert ok, (c.id, reason)
        if c.id in ("d3D3", "d4D3", "d5D3", "d6D3"):
            assert value == c.record
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_problem.py -q`. Expected: FAIL.
- [ ] **Step 3:** Write the four files per the content above.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_problem.py -q`. Expected: pass, in under about 60 s.
- [ ] **Step 5:** Commit with `git add problems/bipartite_dd tests/test_problem.py && git commit -m "feat: bipartite degree-diameter problem plug-in"`, plus the trailer.

---

### Task 5: Runner (one program, one case, one subprocess)

**Files:**
- Create: `evolve/runner.py`, `evolve/_harness.py`
- Test: `tests/test_runner.py`

**Interfaces — Produces:**
```python
# evolve/runner.py
@dataclass
class RunResult:
    status: str          # "ok" | "timeout" | "crash" | "bad_output"
    output: object       # parsed JSON from build(), None unless status == "ok"
    wall_s: float
    error: str           # "" on ok; else the last 2000 chars of stderr or a message

def run_program(program: Path, harness_dir: Path, params: dict, seed: int,
                time_limit: float, grace_s: float = 5.0) -> RunResult
```

Behaviour:
- Make a fresh temp dir. Run:
  `[sys.executable, "-I", str(HARNESS), str(program), str(harness_dir), json.dumps(params), str(seed), str(time_limit), str(out_path)]`
  - `cwd` = the temp dir
  - `stdout=DEVNULL`, stderr to a file in the temp dir
  - `start_new_session=True`
  - env = `os.environ` copy plus `OMP_NUM_THREADS`, `OPENBLAS_NUM_THREADS`, `MKL_NUM_THREADS` and `VECLIB_MAXIMUM_THREADS`, all `"1"`
- Wait `time_limit + grace_s`. On expiry, `os.killpg(pgid, SIGKILL)` and return `timeout`.
- Exit code 0 with a readable JSON out-file gives `ok`. Exit code 2 (written by the harness on serialization failure) or a missing or unreadable out-file gives `bad_output`. Any other exit code gives `crash`.
- Clean up the temp dir.

`evolve/_harness.py`:
- inserts `harness_dir` at `sys.path[0]`
- loads the program with `importlib.util.spec_from_file_location("candidate", program)`
- calls `build(**params, seed=seed, time_limit=time_limit)`
- `json.dump`s the result with `default=_default`, where `_default` converts numpy scalars and arrays via `.tolist()` / `int()` / `float()`, and sets and tuples to lists
- writes to `out_path + ".tmp"`, then renames it
- on `TypeError`/`ValueError`/`OverflowError` during serialization: prints the traceback, exits 2
- any exception in import or `build`: traceback to stderr, exits 1

- [ ] **Step 1: Write the failing tests** in `tests/test_runner.py`:

```python
import time
from pathlib import Path
from evolve.runner import run_program

def prog(tmp_path, body, name="p.py"):
    p = tmp_path / name; p.write_text(body); return p

def test_ok(tmp_path):
    r = run_program(prog(tmp_path, "def build(x, seed, time_limit):\n    return [x, [[0, 1]]]\n"), tmp_path, {"x": 2}, 0, 5)
    assert r.status == "ok" and r.output == [2, [[0, 1]]] and r.error == ""

def test_numpy_output_ok(tmp_path):
    body = "import numpy as np\ndef build(seed, time_limit):\n    return (np.int64(3), [(np.int64(0), 1)], {2})\n"
    r = run_program(prog(tmp_path, body), tmp_path, {}, 0, 5)
    assert r.status == "ok" and r.output == [3, [[0, 1]], [2]]

def test_imports_from_harness_dir(tmp_path):
    lib_dir = tmp_path / "libdir"; lib_dir.mkdir(); (lib_dir / "helper.py").write_text("X = 41\n")
    r = run_program(prog(tmp_path, "import helper\ndef build(seed, time_limit):\n    return helper.X + 1\n"), lib_dir, {}, 0, 5)
    assert r.status == "ok" and r.output == 42

def test_crash(tmp_path):
    r = run_program(prog(tmp_path, "def build(seed, time_limit):\n    raise RuntimeError('boom')\n"), tmp_path, {}, 0, 5)
    assert r.status == "crash" and "boom" in r.error and r.output is None

def test_syntax_error_is_crash(tmp_path):
    r = run_program(prog(tmp_path, "def build(:\n"), tmp_path, {}, 0, 5)
    assert r.status == "crash"

def test_bad_output(tmp_path):
    r = run_program(prog(tmp_path, "def build(seed, time_limit):\n    return object()\n"), tmp_path, {}, 0, 5)
    assert r.status == "bad_output"

def test_timeout(tmp_path):
    t = time.monotonic()
    r = run_program(prog(tmp_path, "import time\ndef build(seed, time_limit):\n    time.sleep(60)\n"), tmp_path, {}, 0, 1, grace_s=1)
    assert r.status == "timeout" and time.monotonic() - t < 10

def test_timeout_kills_grandchild(tmp_path):
    marker = tmp_path / "alive"
    body = f"""import subprocess, sys, time
def build(seed, time_limit):
    subprocess.Popen([sys.executable, '-c', 'import time,pathlib; time.sleep(4); pathlib.Path({str(marker)!r}).write_text("x")'])
    time.sleep(60)
"""
    r = run_program(prog(tmp_path, body), tmp_path, {}, 0, 1, grace_s=0.5)
    assert r.status == "timeout"
    time.sleep(5)
    assert not marker.exists()
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_runner.py -q`. Expected: FAIL.
- [ ] **Step 3:** Implement `runner.py` and `_harness.py`.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_runner.py -q`. Expected: pass.
- [ ] **Step 5:** Commit with `git add evolve/runner.py evolve/_harness.py tests/test_runner.py && git commit -m "feat: sandboxed program runner"`, plus the trailer.

---

### Task 6: Store and selection

**Files:**
- Create: `evolve/store.py`, `evolve/select.py`
- Test: `tests/test_store_select.py`

**Interfaces — Produces:**
```python
# evolve/store.py
@dataclass
class CandidateRecord:
    id: str
    generation: int
    parents: list[str]
    role: str
    fitness: float | None              # None until evaluated
    case_values: dict[str, float]      # case_id -> value (0 if invalid); {} until evaluated
    case_scores: dict[str, float]

class RunStore:
    def __init__(self, root: Path)                 # root = runs/<run_id>
    root: Path
    def init(self, config_text: str) -> None       # mkdir candidates/ generations/; write config.toml if absent
    def candidate_dir(self, cid: str) -> Path
    def program_path(self, cid: str) -> Path
    def add_candidate(self, cid: str, code: str, meta: dict) -> None  # FileExistsError if present; writes program.py then meta.json
    def has_candidate(self, cid: str) -> bool      # meta.json exists
    def read_program(self, cid: str) -> str
    def read_meta(self, cid: str) -> dict
    def has_result(self, cid: str) -> bool
    def write_result(self, cid: str, result: dict) -> None   # result.json, atomic (tmp + rename)
    def read_result(self, cid: str) -> dict
    def load_candidates(self) -> list[CandidateRecord]       # all with meta.json, sorted by id
    def candidates_in_generation(self, g: int) -> list[str]  # sorted ids whose meta generation == g
    def generation_done(self, g: int) -> bool                # generations/{g:03d}.json exists and its "complete" is True
    def write_generation(self, g: int, summary: dict) -> None
    def read_generation(self, g: int) -> dict | None
    def write_plan(self, g: int, plan: dict) -> None         # generations/{g:03d}.plan.json (atomic)
    def read_plan(self, g: int) -> dict | None
    def append_call(self, record: dict) -> None              # one JSON line to calls.jsonl
    def count_calls(self) -> int
    def write_status(self, text: str) -> None                # status.md
```

`meta.json` keys: `id, generation, parents, role, created` (ISO time), `mutator` (a dict). `result.json` keys:
- `cases`: `{case_id: {status, valid, value, score, reason, wall_s}}`
- `fitness`: float

`CandidateRecord.case_values` and `case_scores` come from `result["cases"][*]["value"]` and `["score"]`.

```python
# evolve/select.py
def fitness(case_scores: dict[str, float], cases: list[Case]) -> float
    # sum(w * score) / sum(w) over all cases; a missing case counts as 0
def parent_pool(cands: list[CandidateRecord], cases: list[Case], elite_k: int) -> list[str]
    # Only evaluated candidates with fitness > 0.
    # Elites: sorted by (-fitness, generation, id), first elite_k.
    # Champions: for each case in order, the best candidate by (-value, -fitness, generation, id) with value > 0.
    # Result: elites, then champions not already included, keeping order.
def pick_roles(n: int, weights: dict[str, float], rng: random.Random) -> list[str]
    # rng.choices over sorted(weights) keys, with their weights, k=n
def pick_parents(pool: list[str], role: str, rng: random.Random) -> list[str]
    # "crossover" with len(pool) >= 2: rng.sample(pool, 2); otherwise [rng.choice(pool)]
```

- [ ] **Step 1: Write the failing tests** in `tests/test_store_select.py`:

```python
import random
import pytest
from evolve.store import RunStore, CandidateRecord
from evolve.select import fitness, parent_pool, pick_roles, pick_parents
from evolve.types import Case

CASES = [Case("a", {}, 10, 20, "calibration", 1), Case("b", {}, 10, 20, "target", 2)]

def res(va, vb):
    return {"cases": {"a": {"status": "ok", "valid": True, "value": va, "score": va/10, "reason": "", "wall_s": 0.1},
                      "b": {"status": "ok", "valid": True, "value": vb, "score": vb/10, "reason": "", "wall_s": 0.1}},
            "fitness": fitness({"a": va/10, "b": vb/10}, CASES)}

def test_fitness_weighted():
    assert fitness({"a": 1.0, "b": 0.5}, CASES) == pytest.approx((1.0 + 2*0.5) / 3)
    assert fitness({"a": 1.0}, CASES) == pytest.approx(1/3)

def test_store_roundtrip(tmp_path):
    s = RunStore(tmp_path / "run"); s.init("x = 1\n"); s.init("ignored")
    assert (s.root / "config.toml").read_text() == "x = 1\n"
    s.add_candidate("g000-seed", "def build(): pass\n", {"id": "g000-seed", "generation": 0, "parents": [], "role": "seed", "mutator": {}})
    with pytest.raises(FileExistsError):
        s.add_candidate("g000-seed", "", {})
    assert s.read_program("g000-seed").startswith("def build")
    assert not s.has_result("g000-seed")
    s.write_result("g000-seed", res(10, 5))
    [c] = s.load_candidates()
    assert c.fitness == pytest.approx((1 + 2*0.5)/3) and c.case_values == {"a": 10, "b": 5}
    assert s.candidates_in_generation(0) == ["g000-seed"] and s.candidates_in_generation(1) == []
    assert not s.generation_done(0)
    s.write_generation(0, {"complete": False}); assert not s.generation_done(0)
    s.write_generation(0, {"complete": True}); assert s.generation_done(0)
    s.append_call({"a": 1}); s.append_call({"a": 2}); assert s.count_calls() == 2
    s.write_plan(1, {"tasks": []}); assert s.read_plan(1) == {"tasks": []} and s.read_plan(2) is None

def rec(cid, g, fit, va, vb):
    return CandidateRecord(cid, g, [], "default", fit, {"a": va, "b": vb}, {"a": va/10, "b": vb/10})

def test_parent_pool_keeps_specialist():
    cands = [rec("g001-c00", 1, 0.9, 10, 10), rec("g001-c01", 1, 0.8, 9, 10), rec("g001-c02", 1, 0.2, 0, 12),
             rec("g001-c03", 1, 0.0, 0, 0), CandidateRecord("g001-c04", 1, [], "x", None, {}, {})]
    pool = parent_pool(cands, CASES, elite_k=2)
    assert pool == ["g001-c00", "g001-c01", "g001-c02"]

def test_sampling_deterministic():
    w = {"default": 0.5, "crossover": 0.2, "invent": 0.15, "moonshot": 0.15}
    assert pick_roles(8, w, random.Random(1)) == pick_roles(8, w, random.Random(1))
    assert len(pick_parents(["x", "y", "z"], "crossover", random.Random(2))) == 2
    assert pick_parents(["x"], "crossover", random.Random(2)) == ["x"]
    assert len(pick_parents(["x", "y"], "default", random.Random(2))) == 1
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_store_select.py -q`. Expected: FAIL.
- [ ] **Step 3:** Implement `store.py` and `select.py`.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_store_select.py -q`. Expected: pass.
- [ ] **Step 5:** Commit with `git add evolve/store.py evolve/select.py tests/test_store_select.py && git commit -m "feat: run store and selection"`, plus the trailer.

---

### Task 7: Mutator (prompts, claude -p, fake)

**Files:**
- Create: `evolve/mutator.py`
- Test: `tests/test_mutator.py`, `tests/fake_claude.py` (a stand-in CLI script)

**Interfaces — Produces:**
```python
# evolve/mutator.py
class BudgetStop(Exception):
    def __init__(self, message: str, calls: list[dict] | None = None): ...
    calls: list[dict]

@dataclass
class MutationTask:
    cid: str
    role: str                                   # "default" | "crossover" | "invent" | "moonshot"
    parents: list[tuple[str, str, dict]]        # (parent cid, code, {case_id: value})
    cases: list[Case]

@dataclass
class MutationResult:
    cid: str
    code: str | None
    attempts: int
    calls: list[dict]           # one dict per CLI call (see call record below)
    error: str                  # "" on success

ROLE_INSTRUCTIONS: dict[str, str]
def build_user_prompt(task: MutationTask, previous_code: str | None = None, error: str | None = None) -> str
def extract_code(text: str) -> str | None
def static_check(code: str) -> str | None       # None if OK, else an error message
def parse_stream(stdout: str) -> dict           # {"text", "is_error", "error_status", "error_message", "usage", "cost_usd",
                                                #  "duration_api_ms", "auth", "rate_limits", "model_usage", "session_id"}
def child_env() -> dict

class ClaudeMutator:
    def __init__(self, model: str, system_prompt: str, smoke, timeout_s: float = 300.0,
                 stop_at: float = 0.9, cli: str = "claude", backoff_s: tuple = (2, 8, 30)):
        # smoke: Callable[[str], tuple[bool, str]] -> (ok, error message)
    def mutate(self, task: MutationTask) -> MutationResult   # may raise BudgetStop (with .calls)
    def call(self, prompt: str) -> dict                      # one CLI call -> parse_stream dict + "wall_s"

class FakeMutator:
    def __init__(self, reply, smoke):   # reply: Callable[[MutationTask, int], str]; attempt is 1 or 2
    def mutate(self, task: MutationTask) -> MutationResult
```

The shared mutation flow (both classes share one private helper, `_mutate_with(get_reply, task, smoke)`):
1. Attempt 1: reply = `get_reply(build_user_prompt(task))`. Then `code = extract_code(reply)`. Then `err = "no python code block found"` if code is None, else `static_check(code)`, else `None if smoke(code)[0] else smoke(code)[1]`.
2. If `err` is set: attempt 2 with `build_user_prompt(task, previous_code=code or reply[:4000], error=err)`, checked the same way.
3. Return `MutationResult(cid, code_or_None, attempts, calls, "" or err)`.

`ROLE_INSTRUCTIONS` (verbatim):
- **default:** "Improve the parent program so it scores higher on more cases, especially the targets. Make a focused, meaningful change."
- **crossover:** "You are given two parent programs. Combine their strongest ideas into one program that beats both."
- **invent:** "Invent a new construction idea or helper routine that the parent does not use yet, implement it inside the program, and use it where it helps."
- **moonshot:** "Make a bold, high-risk change: try a substantially different construction for the cases where the parent is weakest. Keep a safe fallback so every case still returns a valid graph."

`build_user_prompt` layout:
- the role instruction
- for each parent: `### Parent {cid}`, a scores table (one line per case: `{case.id} ({kind}, params): {value} / record {record} / ceiling {ceiling}`), then its code in a ```python block
- if `error`: a section `### Your previous attempt failed` with the previous code in a ```python block and the error text
- finally: "Reply with the complete new program in a single ```python code block. Do not include anything after the code block."

`extract_code`:
- Find all fenced blocks with the regex `` ```(?:python|py)?[ \t]*\n(.*?)``` `` (DOTALL).
- Return the last one containing `def build`.
- If there's none, but the text starts with `def build` or `import`, and the text compiles, return the stripped text.
- Otherwise return None.

`static_check`: `compile(code, "candidate.py", "exec")` (on a `SyntaxError`, return `"SyntaxError: ..."` with the line number), then require `re.search(r"^def build\(", code, re.M)`, else return `"no top-level def build(...)"`.

`ClaudeMutator.call`:
- Before calling: if a previous call set `self._limit_hit`, or any stored window utilization is ≥ `stop_at`, raise `BudgetStop`.
- Run `subprocess.run([cli, "-p", "--output-format", "stream-json", "--verbose", "--model", model, "--setting-sources", "", "--strict-mcp-config", "--disable-slash-commands", "--tools", "", f"--system-prompt={system_prompt}"], input=prompt, capture_output=True, text=True, timeout=timeout_s, cwd=~/.cache/claude-p-isolated (mkdir -p), env=child_env())`.
- A timeout gives the result `{"is_error": True, "error_message": "timeout", ...}`.
- Parse with `parse_stream`. Store `rate_limits`.
- If `auth` is present and `!= "none"`, raise `RuntimeError("refusing: claude -p is not using the subscription login (apiKeySource=...)")`.
- If `is_error` and the message matches `/usage limit|limit reached|hit your (\w+ )?limit/i`, set `_limit_hit` and raise `BudgetStop`.
- If `is_error` and the status is 429, 529 or ≥ 500, sleep the next `backoff_s` value and retry (at most `len(backoff_s)` retries; every call is recorded).
- After a successful call, if any utilization ≥ `stop_at`, set `_limit_hit`. The result is still returned, and the next call raises `BudgetStop`.

Call record appended to `MutationResult.calls`: `{"cid", "attempt", "model", "usage", "cost_usd", "duration_api_ms", "wall_s", "is_error", "error_message", "rate_limits"}`. When `BudgetStop` is raised inside `mutate`, it carries the calls made so far.

`parse_stream`:
- Read JSON lines, skipping bad ones.
- `init` = the first event with `type == "system"` and `subtype == "init"`. Its `apiKeySource` becomes `auth`.
- `result` = the last event with `type == "result"`. Its fields map as:
  - `result` → text
  - `is_error`
  - `api_error_status` → `error_status`
  - `result` or `subtype` → `error_message` when `is_error`
  - `usage`
  - `total_cost_usd` → `cost_usd`
  - `duration_api_ms`
  - `modelUsage` → `model_usage`
  - `session_id`
- `rate_limits` = the last `rate_limit_event`'s `rate_limit_info.unifiedWindows` (a dict of `{name: {"utilization": float, ...}}`).
- No result event gives `is_error=True` and `error_message="no result event"`.

`child_env`: a copy of `os.environ` without any key starting with `CLAUDE` or `ANTHROPIC`, except `CLAUDE_CONFIG_DIR` and `CLAUDE_CODE_OAUTH_TOKEN`. It also sets `CLAUDE_CODE_DISABLE_AUTO_MEMORY=1`.

`tests/fake_claude.py` is a stand-in CLI.
- It reads stdin, and reads the env var `FAKE_CLAUDE_MODE`.
- It prints stream-json lines:
  - an init line `{"type":"system","subtype":"init","apiKeySource": <"none", or "ANTHROPIC_API_KEY" when mode == "apikey">}`
  - for mode `limit90`: `{"type":"rate_limit_event","rate_limit_info":{"unifiedWindows":{"five_hour":{"utilization":0.95}}}}`
  - for mode `usage_limit`: a result line with `is_error` true and result `"You've hit your limit"`
  - for mode `transient`: on the first call (tracked by a counter file at `$FAKE_CLAUDE_COUNTER`), a result with `is_error` true and `api_error_status` 529; afterwards a normal result
  - otherwise: `{"type":"result","is_error":false,"result":"Here:\n```python\ndef build(d, D, seed, time_limit):\n    return 1, []\n```","usage":{"input_tokens":10,"output_tokens":5},"total_cost_usd":0.001,"duration_api_ms":50,"modelUsage":{"claude-haiku-5-5":{"outputTokens":5}},"session_id":"s"}`
- It is invoked as `cli=[sys.executable, "tests/fake_claude.py"]`. `ClaudeMutator` accepts `cli` as a str or a list. A list is used as the command prefix.

- [ ] **Step 1: Write the failing tests** in `tests/test_mutator.py`:

```python
import os, sys
import pytest
from evolve.mutator import (extract_code, static_check, parse_stream, build_user_prompt, child_env,
                            MutationTask, FakeMutator, ClaudeMutator, BudgetStop)
from evolve.types import Case

CASES = [Case("d3D3", {"d": 3, "D": 3}, 14, 14, "calibration", 1)]
GOOD = "def build(d, D, seed, time_limit):\n    return 1, []\n"
TASK = MutationTask("g001-c00", "default", [("g000-seed", GOOD, {"d3D3": 14.0})], CASES)
FAKE = [sys.executable, os.path.join(os.path.dirname(__file__), "fake_claude.py")]

def test_extract_code_variants():
    assert extract_code("x\n```python\n" + GOOD + "```\nbye") == GOOD
    two = "```python\nimport os\n```\ntext\n```python\n" + GOOD + "```"
    assert extract_code(two) == GOOD
    assert extract_code("```\n" + GOOD + "```") == GOOD
    assert extract_code("```py\n" + GOOD + "```") == GOOD
    assert extract_code(GOOD) == GOOD.strip()
    assert extract_code("no code here") is None

def test_static_check():
    assert static_check(GOOD) is None
    assert static_check("def build(:\n").startswith("SyntaxError")
    assert static_check("def helper():\n    pass\n") == "no top-level def build(...)"

def test_prompt_contains_parent_scores_and_error():
    p = build_user_prompt(TASK)
    assert "### Parent g000-seed" in p and "d3D3" in p and "record 14" in p and GOOD in p
    p2 = build_user_prompt(TASK, previous_code="bad", error="SyntaxError: x")
    assert "### Your previous attempt failed" in p2 and "SyntaxError: x" in p2

def test_parse_stream():
    out = "\n".join([
        '{"type":"system","subtype":"init","apiKeySource":"none"}',
        'not json',
        '{"type":"rate_limit_event","rate_limit_info":{"unifiedWindows":{"seven_day":{"utilization":0.3}}}}',
        '{"type":"result","is_error":false,"result":"hi","usage":{"output_tokens":1},"total_cost_usd":0.01,"duration_api_ms":9,"modelUsage":{},"session_id":"s"}',
    ])
    r = parse_stream(out)
    assert r["auth"] == "none" and r["text"] == "hi" and not r["is_error"]
    assert r["rate_limits"]["seven_day"]["utilization"] == 0.3 and r["cost_usd"] == 0.01
    assert parse_stream("")["is_error"]

def test_child_env_strips_claude_vars(monkeypatch):
    monkeypatch.setenv("CLAUDE_CODE_SESSION", "x"); monkeypatch.setenv("ANTHROPIC_API_KEY", "k")
    monkeypatch.setenv("CLAUDE_CONFIG_DIR", "/c")
    e = child_env()
    assert "CLAUDE_CODE_SESSION" not in e and "ANTHROPIC_API_KEY" not in e
    assert e["CLAUDE_CONFIG_DIR"] == "/c" and e["CLAUDE_CODE_DISABLE_AUTO_MEMORY"] == "1"

def test_fake_mutator_retry_then_success():
    replies = {1: "sorry no code", 2: "```python\n" + GOOD + "```"}
    m = FakeMutator(lambda task, attempt: replies[attempt], smoke=lambda code: (True, ""))
    r = m.mutate(TASK)
    assert r.code == GOOD and r.attempts == 2 and r.error == ""

def test_fake_mutator_smoke_failure_twice():
    m = FakeMutator(lambda t, a: "```python\n" + GOOD + "```", smoke=lambda code: (False, "crash: boom"))
    r = m.mutate(TASK)
    assert r.code is None and r.attempts == 2 and "boom" in r.error

def test_claude_mutator_with_fake_cli(monkeypatch):
    monkeypatch.delenv("FAKE_CLAUDE_MODE", raising=False)
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    r = m.mutate(TASK)
    assert r.code.startswith("def build") and r.attempts == 1 and len(r.calls) == 1
    assert r.calls[0]["cost_usd"] == 0.001

def test_refuses_api_key(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "apikey")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    with pytest.raises(RuntimeError, match="refusing"):
        m.mutate(TASK)

def test_budget_stop_after_high_utilization(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "limit90")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    m.mutate(TASK)                       # this call succeeds but reports 95% use
    with pytest.raises(BudgetStop):
        m.mutate(TASK)

def test_usage_limit_is_budget_stop(monkeypatch):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "usage_limit")
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE)
    with pytest.raises(BudgetStop) as e:
        m.mutate(TASK)
    assert len(e.value.calls) == 1

def test_transient_error_retried(monkeypatch, tmp_path):
    monkeypatch.setenv("FAKE_CLAUDE_MODE", "transient"); monkeypatch.setenv("FAKE_CLAUDE_COUNTER", str(tmp_path / "n"))
    m = ClaudeMutator("claude-haiku-5-5", "sys", smoke=lambda c: (True, ""), cli=FAKE, backoff_s=(0.01,))
    r = m.mutate(TASK)
    assert r.code is not None and len(r.calls) == 2
```

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_mutator.py -q`. Expected: FAIL.
- [ ] **Step 3:** Implement `evolve/mutator.py` and `tests/fake_claude.py`.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest tests/test_mutator.py -q`. Expected: pass. No real `claude` call is made.
- [ ] **Step 5:** Commit with `git add evolve/mutator.py tests/test_mutator.py tests/fake_claude.py && git commit -m "feat: Haiku mutator over claude -p with fake CLI tests"`, plus the trailer.

---

### Task 8: Config, loop, CLI

Depends on Tasks 5, 6 and 7. Uses `tests/toy_problem.py` from Task 1.

**Files:**
- Create: `evolve/config.py`, `evolve/loop.py`, `evolve/cli.py`, `evolve/__main__.py`, `configs/pilot.toml`, `configs/smoke.toml`
- Test: `tests/test_loop.py`

**Interfaces:**
- Consumes: `run_program`, `RunStore`, `CandidateRecord`, `fitness`, `parent_pool`, `pick_roles`, `pick_parents`, `MutationTask`, `MutationResult`, `ClaudeMutator`, `FakeMutator`, `BudgetStop`, `load_problem`, `CheckerBug`, `CaseScore`.
- Produces:
```python
# evolve/config.py
@dataclass
class RunConfig:
    run_id: str
    problem: str                     # module path, e.g. "problems.bipartite_dd.problem"
    seed: int
    generations: int
    candidates_per_generation: int
    eval_seeds: list[int]
    time_limit_s: float
    workers: int
    mutator: dict                    # kind ("claude"|"fake"), model, concurrency, timeout_s, max_calls, stop_at
    selection: dict                  # elite_k, roles {role: weight}
    git: dict                        # enabled, push
    runs_dir: str = "runs"
    records_dir: str = "records"
    smoke_time_limit_s: float = 5.0
def load_config(path: str | Path) -> tuple[RunConfig, str]   # (config, raw text)

# evolve/loop.py
EXIT_DONE, EXIT_BUDGET, EXIT_CHECKER_BUG = 0, 3, 4
def run(cfg: RunConfig, config_text: str, repo_root: Path, mutator=None, log=print) -> int
def evaluate_candidate(problem, store, cid, cfg) -> dict     # returns result dict as written to result.json
def make_smoke(problem, cfg) -> Callable[[str], tuple[bool, str]]
def render_status(store, problem, cfg) -> str

# evolve/cli.py
def main(argv: list[str] | None = None) -> int
# python -m evolve run CONFIG [--fake]     -> loop.run(...)
# python -m evolve status RUN_DIR          -> prints status.md
```

`configs/pilot.toml`:
```toml
run_id = "pilot-001"
problem = "problems.bipartite_dd.problem"
seed = 1
generations = 10
candidates_per_generation = 12
eval_seeds = [0]
time_limit_s = 20
workers = 8

[mutator]
kind = "claude"
model = "claude-haiku-5-5"
concurrency = 4
timeout_s = 300
max_calls = 400
stop_at = 0.9

[selection]
elite_k = 4
roles = { default = 0.5, crossover = 0.2, invent = 0.15, moonshot = 0.15 }

[git]
enabled = true
push = true
```

`configs/smoke.toml` is the same, except `run_id = "smoke-001"`, `generations = 1`, `candidates_per_generation = 4`, `max_calls = 12` and `[git] enabled = false`.

Loop algorithm (`run`):
1. `problem = load_problem(cfg.problem)`. `store = RunStore(repo_root / cfg.runs_dir / cfg.run_id)`. `store.init(config_text)`.
2. Build the mutator if not supplied:
   - `kind == "claude"`: `ClaudeMutator(model, problem.prompt_context(), make_smoke(problem, cfg), timeout_s, stop_at)`
   - `kind == "fake"`: a `FakeMutator` that returns the first parent's code unchanged inside a ```python block
3. **Generation 0:** if not `generation_done(0)`:
   - if `g000-seed` is missing, add it with the code from `problem.seed_program` and meta `role="seed"`
   - evaluate it if it has no result
   - write the summary
4. **For g in 1..cfg.generations,** skipping any `generation_done(g)`:
   - a. `plan = store.read_plan(g)`. If None:
     - `rng = random.Random(cfg.seed * 1000 + g)`
     - `pool = parent_pool(store.load_candidates(), problem.cases, elite_k)`, or `["g000-seed"]` if empty
     - `roles = pick_roles(N, roles, rng)`
     - tasks = `[{"cid": f"g{g:03d}-c{i:02d}", "role": r, "parents": pick_parents(pool, r, rng), "status": "pending"} ...]`
     - `write_plan`
   - b. **Mutate** every task with `status == "pending"` that has no candidate yet, using a ThreadPoolExecutor(`concurrency`):
     - Submit incrementally. Keep at most `concurrency` tasks in flight, and submit the next one only after one completes (`concurrent.futures.wait(..., return_when=FIRST_COMPLETED)`).
     - Before each submission, if `store.count_calls() >= max_calls`, set `stop = True` and stop submitting.
     - Exceptions from a future (including `BaseException`s such as `KeyboardInterrupt`) propagate, except `BudgetStop`. Never swallow them.
     - Each result: append each call record to `calls.jsonl`.
     - If `code`: `add_candidate(cid, code, meta)`, with `meta["mutator"] = {"attempts", "error", "calls": n}`, and task status `"made"`.
     - Else task status `"failed"` with the error.
     - Write the plan after each completion, under a lock.
     - `BudgetStop`: log its calls, set `stop = True`, and leave that task `"pending"`.
     - `RuntimeError` (auth refusal): propagate, after writing the plan.
   - c. **Evaluate** every candidate in generation g that has no result (`evaluate_candidate`).
   - d. **Write the summary** `{"generation", "complete": not stop, "candidates", "made", "failed", "calls_total": count_calls(), "best_fitness", "best_by_case", "new_records", "elapsed_s"}`.
     - `best_by_case` covers all candidates so far: `{case_id: {"cid", "value", "record"}}`.
     - `new_records` lists `[case_id, cid, value]` where the value is greater than the case record.
   - e. Write status.md (`render_status`). Then git commit (and push), if enabled.
   - f. If `stop`: return `EXIT_BUDGET`.
5. Return `EXIT_DONE`.

On a `CheckerBug` anywhere: write `status.md` with the message on top, git commit if enabled, and return `EXIT_CHECKER_BUG`.

`evaluate_candidate`:
- Run the jobs `(case, seed)` for every case and every `eval_seed` through a ThreadPoolExecutor(`cfg.workers`). Each job is `run_program(store.program_path(cid), problem.harness_dir, case.params, seed, cfg.time_limit_s)`.
- For an `ok` status, call `problem.evaluate(case, output)`, which may raise `CheckerBug` (propagate it).
- Per case, keep the best value over seeds (and its output).
- If `valid and value >= case.record`, then:
  - if `problem.verify(case, output)` is False, mark the case invalid with reason `"second checker disagreed"`
  - otherwise, save the record file `records/<problem.name>/<case.id>/<int(value)>-<run_id>-<cid>.json`, holding `{"case", "value", "run_id", "cid", "seed", "output"}`. Save only if no file in that folder has a value prefix ≥ this value.
- Return `{"cases": {...CaseScore fields...}, "fitness": fitness(scores, problem.cases)}` and write it with `store.write_result`.

`make_smoke(problem, cfg)` returns `smoke(code)`, which:
- writes the code to a temp file
- calls `run_program` on `problem.smoke_case()` with `cfg.smoke_time_limit_s` and `grace_s=2`
- returns `(False, f"{status}: {error[-1500:]}")` if the status is not ok
- otherwise evaluates: if invalid, `(False, f"invalid output on smoke case {case.id}: {reason}")`; otherwise `(True, "")`
- turns a `CheckerBug` into `(True, "")`, so the full evaluation catches it

`render_status`: markdown with:
- run id and the problem
- generations done, and total calls
- a table of `case | kind | record | ceiling | best value | best cid`, marking ties `=` and beats `NEW`
- a table of the last 10 generations: `gen | made | failed | best fitness`

Git, with every command run with `cwd=repo_root`:
- `git add -- runs/<run_id> records`
- `git commit -m "chore(run): <run_id> generation <g> best <fitness:.4f>"` plus the trailer
- if `push`: `git push`

A failing command is logged (`log(...)`) and never raised.

- [ ] **Step 1: Write the failing tests** in `tests/test_loop.py`:

```python
import json
from pathlib import Path
import pytest
from evolve.config import load_config, RunConfig
from evolve.loop import run, EXIT_DONE, EXIT_BUDGET, EXIT_CHECKER_BUG
from evolve.mutator import FakeMutator, BudgetStop, MutationResult

def cfg(**kw):
    base = dict(run_id="t", problem="tests.toy_problem", seed=1, generations=2, candidates_per_generation=3,
                eval_seeds=[0], time_limit_s=5, workers=2,
                mutator={"kind": "fake", "concurrency": 2, "max_calls": 100},
                selection={"elite_k": 2, "roles": {"default": 1.0}}, git={"enabled": False, "push": False})
    base.update(kw); return RunConfig(**base)

def better(task, attempt):   # returns x*2+1 → beats records (6 and 10) by 1
    return "```python\nimport helper\ndef build(x, seed, time_limit):\n    return helper.double(x) + 1\n```"

def ok_smoke(code): return (True, "")

def test_load_config_files():
    c, text = load_config("configs/pilot.toml")
    assert c.mutator["model"] == "claude-haiku-5-5" and c.generations >= 1 and "pilot" in text
    s, _ = load_config("configs/smoke.toml")
    assert s.git["enabled"] is False

def test_full_run_and_records(tmp_path):
    rc = run(cfg(), "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None)
    assert rc == EXIT_DONE
    root = tmp_path / "runs" / "t"
    for g in range(3):
        assert json.loads((root / "generations" / f"{g:03d}.json").read_text())["complete"]
    assert len(list((root / "candidates").iterdir())) == 1 + 3 + 3
    s1 = json.loads((root / "generations" / "001.json").read_text())
    assert s1["best_by_case"]["c2"]["value"] == 11 and ["c2", s1["best_by_case"]["c2"]["cid"], 11] in s1["new_records"]
    assert list((tmp_path / "records" / "toy" / "c2").glob("11-t-*.json"))
    assert "NEW" in (root / "status.md").read_text()

class Crashy:
    def __init__(self, n): self.n = n; self.inner = FakeMutator(better, ok_smoke)
    def mutate(self, task):
        self.n -= 1
        if self.n < 0: raise KeyboardInterrupt
        return self.inner.mutate(task)

def test_resume_after_crash(tmp_path):
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 100})
    with pytest.raises(KeyboardInterrupt):
        run(c, "x", tmp_path, mutator=Crashy(4), log=lambda *a: None)
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    root = tmp_path / "runs" / "t"
    cids = sorted(p.name for p in (root / "candidates").iterdir())
    assert cids == ["g000-seed", "g001-c00", "g001-c01", "g001-c02", "g002-c00", "g002-c01", "g002-c02"]
    assert all((root / "candidates" / cid / "result.json").exists() for cid in cids)

class Budgety:
    def __init__(self): self.n = 0; self.inner = FakeMutator(better, ok_smoke)
    def mutate(self, task):
        self.n += 1
        if self.n == 3: raise BudgetStop("limit", calls=[{"cid": task.cid}])
        return self.inner.mutate(task)

def test_budget_stop_then_resume(tmp_path):
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 100})
    assert run(c, "x", tmp_path, mutator=Budgety(), log=lambda *a: None) == EXIT_BUDGET
    root = tmp_path / "runs" / "t"
    assert json.loads((root / "generations" / "001.json").read_text())["complete"] is False
    assert run(c, "x", tmp_path, mutator=FakeMutator(better, ok_smoke), log=lambda *a: None) == EXIT_DONE
    assert json.loads((root / "generations" / "001.json").read_text())["complete"] is True

def test_max_calls_stops(tmp_path):
    class Counting:
        def __init__(self): self.inner = FakeMutator(better, ok_smoke)
        def mutate(self, task):
            r = self.inner.mutate(task); r.calls = [{"cid": task.cid}]; return r
    c = cfg(mutator={"kind": "fake", "concurrency": 1, "max_calls": 2})
    assert run(c, "x", tmp_path, mutator=Counting(), log=lambda *a: None) == EXIT_BUDGET

def test_checker_bug_exit(tmp_path):
    huge = lambda t, a: "```python\ndef build(x, seed, time_limit):\n    return 1000\n```"
    assert run(cfg(), "x", tmp_path, mutator=FakeMutator(huge, ok_smoke), log=lambda *a: None) == EXIT_CHECKER_BUG

def test_failed_mutations_counted(tmp_path):
    nocode = lambda t, a: "no code"
    assert run(cfg(generations=1), "x", tmp_path, mutator=FakeMutator(nocode, ok_smoke), log=lambda *a: None) == EXIT_DONE
    s = json.loads((tmp_path / "runs" / "t" / "generations" / "001.json").read_text())
    assert s["made"] == 0 and s["failed"] == 3
```

Note: `tests/toy_problem.py` (Task 1) has `name = "toy"`. Its `harness_dir` holds `helper.py`, so `import helper` works. `record` is 6 and 10, `ceiling` is 100 for both cases, and an output of 1000 raises `CheckerBug`.

- [ ] **Step 2:** Run `.venv/bin/python -m pytest tests/test_loop.py -q`. Expected: FAIL.
- [ ] **Step 3:** Implement `config.py`, `loop.py`, `cli.py`, `__main__.py` and both configs.
- [ ] **Step 4:** Run `.venv/bin/python -m pytest -q` (the whole suite). Expected: all pass.
- [ ] **Step 5:** Commit with `git add evolve configs tests/test_loop.py && git commit -m "feat: evolution loop, config and CLI"`, plus the trailer.

---

### Task 9: Real smoke run (coordinator)

- [ ] Full suite green: `.venv/bin/python -m pytest -q`.
- [ ] Fake end to end with the real problem: `.venv/bin/python -m evolve run configs/smoke.toml --fake`. Expect exit 0, and seed fitness printed for 13 cases. Then `rm -rf runs/smoke-001`.
- [ ] One real Haiku generation: `.venv/bin/python -m evolve run configs/smoke.toml`. Check:
  - `calls.jsonl` shows calls with `is_error` false (the mutator would have refused if `apiKeySource` weren't `"none"`)
  - the model is `claude-haiku-5-5`
  - candidates evaluated
- [ ] Read 2 of Haiku's programs to judge the prompt quality. Fix the prompt or notes if replies are badly off (e.g. missing code blocks, or ignoring `lib`).
- [ ] Measure: calls, tokens and cost per call, the broken rate, and the generation wall time. Check `claude_compute.py status` for the account reading.
- [ ] Commit any prompt fixes, then push.

### Task 10: Pilot (coordinator)

- [ ] `.venv/bin/python -m evolve run configs/pilot.toml`, in the background, with a watcher per the user's CLAUDE.md (for runs over 10 min).
- [ ] When done: read `status.md` and the summaries. Check any `records/` entries with both checkers again by hand.
- [ ] Report to the user: what climbed, the best per case vs the records, cost per call and in total, the broken rate, and the recommended next step.
