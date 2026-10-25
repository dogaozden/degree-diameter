# degree-diameter

New records for the **bipartite degree–diameter problem**: our graphs beat the published table in **73 of the 83 cells** that
are not already known to be optimal (Δ ≤ 16, D ≤ 10). They were found by Claude Code agents, using evolutionary search,
group-theoretic computer search, finite geometry, and new constructions. Every graph is checked independently, and 28 of them
are also proved in Lean 4 (most of the others are too large for kernel-checked certificates; a few proofs are in progress).

**See it:** [dogaozden.com/degree-diameter](https://dogaozden.com/degree-diameter/) shows the first eight records in 3D and
how the search found them (that page predates most of the results below).

## The problem

Build the largest graph you can such that

1. it is **bipartite**: every vertex is one of two colours and every edge joins the two colours;
2. every vertex has at most **Δ** neighbours;
3. any two vertices are joined by a path of at most **D** edges (the diameter).

The largest possible size, N<sup>b</sup>(Δ, D), is unknown for almost every (Δ, D). The best known graphs are
collected in the Combinatorics Wiki's
[bipartite degree–diameter table](http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs).
A record is a lower bound: one valid graph that is bigger than the table entry. Of the table's 112 cells, 29 are
optimal (the Moore bound is reached), so 83 can still be improved.

## Results

"Table" is the value in the 2013 survey table (DS14v2) that the wiki reproduces. "Lean" is ✓ when the graph at that size is
proved in Lean; a number in brackets is the largest earlier value of the cell proved in Lean. Graph files, builders and
check logs are in this repository (see [How the graphs are checked](#how-the-graphs-are-checked)); the history of every
record, with dates and checks, is in [`research/RESULTS.md`](research/RESULTS.md).

| (Δ, D) | Table | Ours | Gain | Method | Lean |
|---|---:|---:|---:|---|:---:|
| (11, 3) | 190 | **192** | +1.1% | finite geometry | ✓ |
| (13, 3) | 274 | **276** | +0.7% | finite geometry | ✓ |
| (15, 3) | 374 | **376** | +0.5% | finite geometry | ✓ |
| (16, 3) | 394 | **396** | +0.5% | finite geometry | ✓ |
| (7, 4) | 346 | **359** | +3.8% | evolutionary search | ✓ |
| (11, 4) | 1,734 | **1,782** | +2.8% | finite geometry | ✓ |
| (13, 4) | 3,064 | **3,146** | +2.7% | finite geometry | ✓ |
| (15, 4) | 4,946 | **5,070** | +2.5% | finite geometry | ✓ |
| (16, 4) | 5,134 | **5,440** | +6.0% | orbit search (Haar) | ✓ |
| (4, 5) | 160 | **162** | +1.2% | evolutionary search | ✓ |
| (5, 5) | 336 | **354** | +5.4% | evolutionary search | ✓ |
| (7, 5) | 1,134 | **1,152** | +1.6% | Haar graph, hand-picked group | ✓ |
| (8, 5) | 1,710 | **2,048** | +19.8% | route-chart lift | (1,764) |
| (9, 5) | 2,496 | **2,662** | +6.7% | Haar graph, hand-picked group | ✓ |
| (10, 5) | 4,000 | **4,800** | +20.0% | generalized quadrangle construction ¹ | — |
| (11, 5) | 5,850 | **7,020** | +20.0% | generalized quadrangle construction ¹ | — |
| (12, 5) | 8,200 | **9,840** | +20.0% | generalized quadrangle construction ¹ | — |
| (13, 5) | 11,480 | **11,486** | +0.1% | finite geometry (unit design) ¹ | — |
| (14, 5) | 14,760 | **17,568** | +19.0% | generalized quadrangle construction ¹ | — |
| (15, 5) | 20,496 | **20,736** | +1.2% | route-chart lift | — |
| (16, 5) ² | 27,300 | **33,792** | +23.8% | route-chart lift ¹ | — |
| (7, 6) | 8,992 | **9,592** | +6.7% | finite geometry | ✓ |
| (11, 6) | 142,464 | **148,944** | +4.5% | finite geometry | — |
| (13, 6) | 374,452 | **388,972** | +3.9% | finite geometry | — |
| (15, 6) | 842,048 | **870,440** | +3.4% | finite geometry | — |
| (16, 6) | 884,062 | **940,846** | +6.4% | finite geometry | — |
| (4, 7) | 840 | **864** | +2.9% | vertex-transitive (Cayley-type) | — |
| (5, 7) | 3,110 | **3,120** | +0.3% | voltage lift / metacyclic Haar | ✓ |
| (6, 7) | 8,310 | **8,880** | +6.9% | orbit search (Haar) | ✓ |
| (7, 7) | 23,436 | **23,598** | +0.7% | hexagon cover + hub vertices ¹ | — |
| (8, 7) | 40,586 | **43,344** | +6.8% | orbit search (Haar) | ✓ |
| (9, 7) | 117,648 | **118,238** | +0.5% | hexagon cover + hub vertices ¹ | — |
| (10, 7) | 224,694 | **225,152** | +0.2% | hexagon cover + hub vertices ¹ | — |
| (11, 7) | 398,580 | **413,180** | +3.7% | hexagon cover + hub vertices ¹ | — |
| (12, 7) | 664,300 | **693,500** | +4.4% | hexagon cover + hub vertices ¹ | — |
| (13, 7) | 1,062,936 | **1,064,472** | +0.1% | hexagon cover + hub vertices ¹ | — |
| (14, 7) | 1,771,560 | **1,789,588** | +1.0% | hexagon cover + hub vertices ¹ | — |
| (15, 7) | 2,480,184 | **2,501,124** | +0.8% | hexagon cover + hub vertices ¹ | — |
| (16, 7) | 4,022,340 | **4,052,108** | +0.7% | hexagon cover + hub vertices ¹ | — |
| (3, 8) ² | 256 | **288** | +12.5% | voltage lift / metacyclic Haar | ✓ |
| (5, 8) | 9,234 | **9,760** | +5.7% | evolutionary search | (9,576) |
| (6, 8) | 29,790 | **31,680** | +6.3% | orbit search (Haar) ¹ | (30,576) |
| (7, 8) | 80,940 | **95,760** | +18.3% | orbit search (Haar) | ✓ |
| (8, 8) | 201,480 | **239,904** | +19.1% | orbit search (Haar) | ✓ |
| (9, 8) | 449,480 | **540,360** | +20.2% | orbit search (Haar) | ✓ |
| (11, 8) | 2,246,940 | **2,258,520** | +0.5% | orbit search (Haar) | — |
| (13, 8) | 5,314,680 | **6,999,552** | +31.7% | finite geometry | — |
| (15, 8) | 14,172,480 | **18,128,880** | +27.9% | orbit search (Haar) | — |
| (5, 9) | 27,936 | **29,480** | +5.5% | evolutionary search | (28,560) |
| (6, 9) | 117,360 | **127,296** | +8.5% | orbit search (Haar) | ✓ |
| (7, 9) | 400,160 | **462,840** | +15.7% | orbit search (Haar) | ✓ |
| (8, 9) | 1,091,232 | **1,341,600** | +22.9% | evolutionary search | — |
| (9, 9) | 2,961,536 | **3,499,776** | +18.2% | orbit search (Haar) | — |
| (10, 9) | 7,057,400 | **8,003,856** | +13.4% | orbit search (Haar) | — |
| (11, 9) | 15,200,448 | **16,792,080** | +10.5% | orbit search (Haar) | — |
| (12, 9) | 30,001,152 | **34,026,720** | +13.4% | orbit search (Haar) | — |
| (13, 9) | 50,990,610 | **67,742,688** | +32.9% | orbit search (Haar) | — |
| (14, 9) | 95,087,738 | **116,068,656** | +22.1% | orbit search (Haar) | — |
| (15, 9) | 168,016,334 | **208,029,120** | +23.8% | orbit search (Haar) | — |
| (16, 9) | 288,939,118 | **337,394,400** | +16.8% | orbit search (Haar) | — |
| (4, 10) | 11,748 | **12,416** | +5.7% | voltage lift / metacyclic Haar | ✓ |
| (5, 10) | 90,068 | **95,472** | +6.0% | voltage lift / metacyclic Haar | ✓ |
| (6, 10) | 452,032 | **524,160** | +16.0% | orbit search (Haar) | ✓ |
| (7, 10) | 1,987,380 | **2,237,760** | +12.6% | finite geometry ¹ | — |
| (8, 10) | 6,927,210 | **7,818,096** | +12.9% | finite geometry ¹ | — |
| (9, 10) | 20,017,260 | **23,975,280** | +19.8% | orbit search (Haar) | — |
| (10, 10) | 50,331,156 | **60,141,120** | +19.5% | orbit search (Haar) | — |
| (11, 10) | 0 | **148,729,680** | new | finite geometry ¹ | — |
| (12, 10) | 300,383,050 | **325,832,976** | +8.5% | orbit search (Haar) | — |
| (13, 10) | 617,330,936 | **677,714,400** | +9.8% | orbit search (Haar) | — |
| (14, 10) | 1,213,477,190 | **1,326,627,120** | +9.3% | orbit search (Haar) | — |
| (15, 10) | 2,300,326,510 | **2,467,618,800** | +7.3% | finite geometry ¹ | — |
| (16, 10) | 4,119,507,330 | **4,220,872,800** | +2.5% | finite geometry ¹ | — |

¹ Found in a session that could call squads of Claude Haiku helpers (see [Opus with Haiku squads](#opus-with-haiku-squads)).
² (3, 8): 288 against 256 is a large jump for a well-studied cell; a literature check for newer values is pending.
(16, 5): beats the table's 27,300 and also two larger graphs we know of, the bipartite flag graph of PG(4,3) (31,460;
Cames van Batenburg–Korsky, 2026) and a double cover of LANL's (16, 4) graph (32,768).

The first eight records (Oct 10, 2026) were checked against the literature
([`records/bipartite_dd/CANDIDATES.md`](records/bipartite_dd/CANDIDATES.md)). For the later ones, a literature check for
values published after 2013 is still pending, so some cells may have been improved elsewhere. None of these results are in the
published table yet.

## How the records were found

- **Evolutionary search** ([`evolve/`](evolve/)): Claude Haiku agents rewrite graph-building programs in up to 68 cloud
  "islands" (AlphaEvolve-style). This found the first records at D = 3, 4 and 5.
- **Finite geometry** ([`research/plus2/`](research/plus2/), [`research/geometry/`](research/geometry/),
  [`research/p4/`](research/p4/)): Claude Opus turned patterns in those records into constructions on projective planes,
  generalized quadrangles and hexagons. That gave the +2 theorem (below), "hats" and "whiskers", and the D = 3, 4 and 6 cells.
- **Haar graphs and the C search** ([`research/frontier/`](research/frontier/)): a Haar graph is built from a group G and a set S
  of Δ elements. `haar_gen3` anneals S over groups like SL(2,q) × Zₙ, with the diameter checked by a bitset BFS. A measured
  size law (`SIZE_LAW.md`) explains where random S stops working.
- **Orbit search** ([`research/structured/`](research/structured/)): S closed under a group automorphism. This broke the
  random-search wall and raised most D = 7–10 cells, up to (14, 10) at 1.33 billion vertices. The theory of why it works is in
  [`research/theory/`](research/theory/).
- **Voltage lifts and metacyclic Haar graphs** ([`research/lifts/`](research/lifts/)): these gave the small-degree cells
  (Δ = 3–5, D = 7–10).
- **Route-chart lifts** ([`research/theorems/`](research/theorems/)): lifts of a small controller graph whose edges carry
  "chart letters" over a finite field (Δ = letters × field size). These gave (16, 5) first, then (8, 5), (12, 5) and (15, 5).
- **Generalized quadrangles at D = 5** ([`research/d10D7/DM_D5.md`](research/d10D7/DM_D5.md)): a construction from a generalized
  quadrangle of order q gave (10, 5), (11, 5), (12, 5) and (14, 5), about 20% above the table.
- **Hexagon + hub vertices** ([`research/squads/exp2/hexd7/`](research/squads/exp2/hexd7/)): the table's D = 7 values are three
  copies of a generalized hexagon H(q). Freeing a point–line pair and adding two hub vertices gains 2 vertices per pair,
  with a short proof. This gave (7, 7), (9, 7) and (11, 7).

### Opus with Haiku squads

In the later runs, a Claude Opus session could call squads of 8 Claude Haiku helpers, each trying one different idea, scored
by a fast checker ([`.claude/skills/haiku-squad`](.claude/skills/haiku-squad/SKILL.md)). Two small controlled comparisons
were run: Opus alone, Opus with squads, and Haikus with no Opus. On (16, 5), only the squad arm built a graph of its own
above 31,460. On the three D = 7 cells, at equal measured budget, both Opus arms beat all three cells and the squad arm went
further in each, while Haikus alone beat none. Notes: [`research/squads/`](research/squads/).

## The +2 theorem

> For every finite projective plane of order q ≥ 4 there is a bipartite graph with 2(q² + q + 6) vertices,
> maximum degree q + 2 and diameter 3.

Araujo-Pardo and López (2022) built such graphs with 2(q² + q + 5) vertices and asked readers to improve the
construction. The search found graphs exactly 2 larger at q = 9, 11 and 13. All three add a fourth "hat" pair
(a copy of a point and a copy of a line) and rotate three incidences to make room. The general rule, its proof
and computer checks are in [`research/plus2/REPORT.md`](research/plus2/REPORT.md); a short note for
mathematicians is in [`research/plus2/note/`](research/plus2/note/).

## Checked in Lean

`lean/` is a Lean 4 + Mathlib project. Each record theorem has the form `∃ G : SimpleGraph (Fin n), IsBipartiteDegDiam G Δ D`.

- [`lean/BipartiteDD/Records.lean`](lean/BipartiteDD/Records.lean) proves the first eight records, by a checker proved
  sound once and run in the kernel (`decide +kernel`, no `native_decide`).
- [`lean/BipartiteDD/Haar/`](lean/BipartiteDD/Haar/) proves the larger Haar and lift records. A general lemma reduces the
  diameter of a Haar graph to a covering condition in the group, which kernel-checked certificates then verify. Briefs and
  status notes: [`research/lean-haarD/`](research/lean-haarD/).
- [`lean/BipartiteDD/Plus2/`](lean/BipartiteDD/Plus2/) proves the +2 theorem for every finite projective plane.

Every theorem's `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (`Axioms.out.txt` files next to the
proofs). No `sorry`, `admit` or `native_decide`.

## How the graphs are checked

Every record is checked by code independent of the code that found it:

- **Haar graphs** (`research/frontier/sols/*.txt`): `research/frontier/build_haar2.py` and the independent
  `check_haar_indep.py`. Above about 20 million vertices, two independently written low-memory checkers
  (`haarcheck_sl.c` / `haarcheck_psl.c` and `bigcheck_indep.c`) run in the cloud, with reports in
  `research/frontier/runs/cloudcheck/`.
- **Other graphs** (lifts, geometry, hexagon, route charts): rebuilt from their builder, then checked by an all-pairs BFS that
  assumes no symmetry ([`research/lifts/coordinator_check/apsp.c`](research/lifts/coordinator_check/apsp.c)). Each also fails,
  as it should, when the diameter limit is lowered by one. Logs: `research/coordinator_check/`, `research/lifts/coordinator_check/`,
  `research/theorems/coordinator_check/`, `research/squads/exp2/coordinator_check/`.
- **The first eight records** also passed three independent checkers (bitsets, networkx, and a from-scratch BFS from every
  vertex).

## Reproduce

```bash
python -m venv .venv && .venv/bin/pip install numpy networkx pytest

# check a record graph with all three checkers
.venv/bin/python scripts/verify_record.py records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json 7 4

# run the tests
.venv/bin/python -m pytest -q

# rebuild the +2 graphs for q = 4 … 16
.venv/bin/python research/plus2/construction.py

# build the Lean proofs (needs elan; downloads Mathlib's cache)
cd lean && lake exe cache get && lake build
```

Running the search itself needs the [Claude Code](https://claude.com/claude-code) CLI: the mutator calls
`claude -p --model claude-haiku-5-5`. `python -m evolve run CONFIG --fake` runs the loop with a stand-in mutator, for
testing without model calls:

```bash
.venv/bin/python -m evolve run configs/smoke.toml --fake
.venv/bin/python -m evolve status runs/smoke-001
```

To check a Haar record or any edge list:

```bash
python3 research/frontier/build_haar2.py research/frontier/sols/d8D9_sl_37_13_orb3_s1.txt /tmp/edges.txt
cc -O2 -o apsp research/lifts/coordinator_check/apsp.c && ./apsp /tmp/edges.txt 8 9
```

## Layout

| Path | What it is |
|---|---|
| `evolve/`, `problems/bipartite_dd/`, `configs/` | the evolutionary engine, the problem plug-in, run configs |
| `records/bipartite_dd/` | the first eight record graphs, their programs, and the literature check |
| `research/frontier/` | Haar search (C), size law, solution files (`sols/`), checkers, cloud check reports |
| `research/structured/` | orbit search |
| `research/theory/`, `research/theorems/` | theory of the searches; theorem search, route-chart lifts, flag graphs |
| `research/lifts/` | voltage lifts and metacyclic Haar graphs |
| `research/squads/` | Opus + Haiku squad runs and the comparisons, incl. the D = 7 hexagon construction |
| `research/plus2/`, `research/geometry/`, `research/p4/` | finite-geometry constructions and proofs |
| `research/lean-haarD/` | Lean briefs, generators and status notes |
| `lean/` | Lean proofs |
| `scripts/`, `tools/`, `tests/` | verification and helpers |

Cloud sessions pushed their work to their own `claude/*` branches; verified results are merged into `master`.

## Credits

Doğa Özden, with Claude Code: Claude Opus 5.5 coordinating, searching and proving, and Claude Haiku 5.5 searching, checking
and writing Lean. Prior work: the table's authors and the Combinatorics Wiki's maintainers.

## License

Code (`evolve/`, `problems/`, `scripts/`, `tests/`, `lean/`) is under the [MIT License](LICENSE). The record
graphs, run logs, research write-ups, pages and documents are under
[CC BY 4.0](LICENSE-DATA): reuse them freely, with credit.
