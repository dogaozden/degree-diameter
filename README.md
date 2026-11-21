# degree-diameter

Large graphs for the **degree–diameter problem**: given a maximum degree Δ and a diameter D, how many vertices can a graph have?
This repository holds new lower bounds, the graphs behind them, the programs that check them, and Lean 4 proofs for many of them.
The graphs were found by Claude agents. Each one is rebuilt and checked by an exact breadth-first search (BFS) in code independent of the
code that found it, and many are also proved in Lean 4.

**Where things stand (20 November 2026)**

- **Bipartite problem: records in 169 cells.**
  75 are cells of the Combinatorics Wiki's bipartite table (of its 83 cells not known to be optimal, Δ ≤ 16, D ≤ 10), for example
  (13, 9): 67,742,688 against 50,990,610 (+32.9%). The other 94 are beyond the table (Δ > 16 or D > 10), up to 30.5 billion vertices at (20, 10).
  Full list: [`records/RECORDS.csv`](records/RECORDS.csv). What was checked against the literature, and what was not, is spelled out
  [below](#caveats-what-has-been-checked-against-the-literature).
- **General (non-bipartite) problem: nine new records, found on 20–21 November 2026:**
  (8, 7) **139,965** (previously 139,867), (10, 7) **625,733** (625,464), (10, 8) **4,538,823** (4,524,979), (12, 8) **19,240,407**
  (19,218,539), (10, 9) **34,934,046** (34,913,494), (7, 9) **1,338,558** (1,332,774), (7, 10) **6,692,790** (6,645,690),
  (9, 10) **90,493,830** (89,658,816) and (8, 10) **27,036,394** (27,019,307), each against the value in
  [Comellas's table](https://web.mat.upc.edu/francesc.comellas/delta-d/table_degree_diameter.html) as fetched the day it was found.
  Details and how to check them: [below](#general-graph-records).
- **Lean 4:** 23 of the bipartite table records below, and (3, 11) and (3, 12) beyond the table, are proved in Lean at the stated size.
- The wiki's bipartite page (last edited February 2022) does not list the bipartite records yet, and Comellas's table does not list the general ones.

**Notes for readers** (drafts, Oct 2026; full proofs and coordinates, with what is proved, computed and Lean-checked):
[polished results, D = 3–6](papers/Ozden_polished_results.pdf) ·
[diameter 7 from the split Cayley hexagon](papers/Ozden_D7_hexagon.pdf) ·
[Haar graphs, D = 8–10](papers/Ozden_Haar_D8-10.pdf) ·
[Gómez's ΩH_q and the D = 8 entries (1 page)](papers/Ozden_OmegaH_D8_note.pdf).

**See it:** [dogaozden.com/math/degree-diameter](https://dogaozden.com/math/degree-diameter/) shows the first eight records in 3D and
how the search found them (that page predates most of the results below). Every record, live:
[dogaozden.com/live/degree-diameter](https://dogaozden.com/live/degree-diameter/).

## The problem

Build the largest graph you can such that

1. every vertex has at most **Δ** neighbours;
2. any two vertices are joined by a path of at most **D** edges (the diameter);
3. for the **bipartite** version, every vertex is one of two colours and every edge joins the two colours.

The largest possible size is unknown for almost every (Δ, D). The best known graphs are collected in the Combinatorics Wiki's
[bipartite table](http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs) (112 cells, 29 of them optimal:
the Moore bound is reached) and in [Comellas's table](https://web.mat.upc.edu/francesc.comellas/delta-d/table_degree_diameter.html)
for general graphs. A record is a lower bound: one valid graph that is bigger than the table entry.

## Bipartite records in the wiki table

"Table" is the value in the Combinatorics Wiki table as last edited in February 2022: the 2013 survey table (Miller–Širáň, DS14v2)
with the 2021 changes at (13, 3) and (15, 3) (270 → 274 and 370 → 374, Araujo-Pardo–López). "Lean" is ✓ when the graph at that size
is proved in Lean; a number in brackets is the largest earlier value of the cell proved in Lean. The history of every record, with
dates and checks, is in [`research/RESULTS.md`](research/RESULTS.md) (up to 2 November).

| (Δ, D) | Table | Ours | Gain | Method | Lean |
|---|---:|---:|---:|---|:---:|
| (3, 8) ² | 256 | **288** | +12.5% | voltage lift / metacyclic Haar | ✓ |
| (3, 10) | 800 | **810** | +1.3% | voltage lift (squad search) | — |
| (4, 5) | 160 | **162** | +1.2% | evolutionary search | ✓ |
| (4, 7) | 840 | **864** | +2.9% | vertex-transitive (Cayley-type) | — |
| (4, 10) | 11,748 | **12,416** | +5.7% | voltage lift / metacyclic Haar | ✓ |
| (5, 5) | 336 | **384** | +14.3% | voltage lift of a 4-vertex base by a group of order 96 | [354] |
| (5, 7) | 3,110 | **3,120** | +0.3% | voltage lift / metacyclic Haar | ✓ |
| (5, 8) | 9,234 | **9,760** | +5.7% | evolutionary search | (9,576) |
| (5, 9) | 27,936 | **29,756** | +6.5% | metacyclic Haar graph | ✓ |
| (5, 10) | 90,068 | **95,472** | +6.0% | voltage lift / metacyclic Haar | ✓ |
| (6, 5) | 684 | **704** | +2.9% | lift of a 4-vertex base graph by C₁₁ × M₁₆ | — |
| (6, 7) | 8,310 | **8,880** | +6.9% | orbit search (Haar) | ✓ |
| (6, 8) | 29,790 | **31,680** | +6.3% | orbit search (Haar) | (30,576) |
| (6, 9) | 117,360 | **127,296** | +8.5% | orbit search (Haar) | ✓ |
| (6, 10) | 452,032 | **524,160** | +16.0% | orbit search (Haar) | ✓ |
| (7, 4) | 346 | **359** | +3.8% | evolutionary search | ✓ |
| (7, 5) | 1,134 | **1,312** | +15.7% | Haar graph of C41 : C16 with a self-dual connection set (a bipartite Cayley graph) | [1,200] |
| (7, 6) | 8,992 | **9,592** | +6.7% | finite geometry | ✓ |
| (7, 7) | 23,436 | **23,598** | +0.7% | hexagon cover + hub vertices | — |
| (7, 8) | 80,940 | **95,760** | +18.3% | orbit search (Haar) | ✓ |
| (7, 9) | 400,160 | **462,840** | +15.7% | orbit search (Haar) | ✓ |
| (7, 10) | 1,987,380 | **2,298,240** | +15.6% | Haar graph of SL(2,7) × PSL(2,19) | — |
| (8, 5) | 1,710 | **2,048** | +19.8% | route-chart lift | (1,764) |
| (8, 7) | 40,586 | **43,344** | +6.8% | orbit search (Haar) | ✓ |
| (8, 8) | 201,480 | **239,904** | +19.1% | orbit search (Haar) | ✓ |
| (8, 9) | 1,091,232 | **1,341,600** | +22.9% | evolutionary search | — |
| (8, 10) | 6,927,210 | **8,043,840** | +16.1% | Haar graph of PSL(2,7) × PSL(2,19) × Z₇ | — |
| (9, 5) | 2,496 | **3,036** | +21.6% | Haar graph of C69 : C22 with a self-dual connection set (a bipartite Cayley graph) | (2,758) |
| (9, 7) | 117,648 | **118,238** | +0.5% | hexagon cover + hub vertices | — |
| (9, 8) | 449,480 | **546,720** | +21.6% | Haar graph of SL(2,16) × Z₆₇ | [540,360] |
| (9, 9) | 2,961,536 | **3,499,776** | +18.2% | orbit search (Haar) | — |
| (9, 10) | 20,017,260 | **24,099,600** | +20.4% | orbit search (Haar) | — |
| (10, 5) | 4,000 | **4,800** | +20.0% | generalized quadrangle construction | — |
| (10, 7) | 224,694 | **225,152** | +0.2% | hexagon cover + hub vertices | — |
| (10, 8) ¹ | 1,176,480 | **1,185,408** | +0.8% | Haar graph of PSL(2,7) × SL(2,8) × Z₇ | — |
| (10, 9) | 7,057,400 | **8,418,120** | +19.3% | orbit search (Haar) | — |
| (10, 10) | 50,331,156 | **64,294,560** | +27.7% | orbit search (Haar) | — |
| (11, 3) | 190 | **192** | +1.1% | finite geometry | ✓ |
| (11, 4) | 1,734 | **1,782** | +2.8% | finite geometry | ✓ |
| (11, 5) | 5,850 | **7,020** | +20.0% | generalized quadrangle construction | — |
| (11, 6) | 142,464 | **148,944** | +4.5% | finite geometry | — |
| (11, 7) | 398,580 | **413,180** | +3.7% | hexagon cover + hub vertices | — |
| (11, 8) | 2,246,940 | **2,258,520** | +0.5% | orbit search (Haar) | — |
| (11, 9) | 15,200,448 | **17,323,152** | +14.0% | orbit search (Haar) | — |
| (11, 10) | 130,592,354 | **157,835,304** | +20.9% | Haar graph of PSL(2,243) × Z₁₁ | — |
| (12, 5) | 8,200 | **9,840** | +20.0% | generalized quadrangle construction | — |
| (12, 7) | 664,300 | **693,500** | +4.4% | hexagon cover + hub vertices | — |
| (12, 9) | 30,001,152 | **35,445,648** | +18.1% | orbit search (Haar) | — |
| (12, 10) | 300,383,050 | **332,797,296** | +10.8% | orbit search (Haar) | — |
| (13, 3) | 274 | **276** | +0.7% | finite geometry | ✓ |
| (13, 4) | 3,064 | **3,146** | +2.7% | finite geometry | ✓ |
| (13, 5) | 11,480 | **11,700** | +1.9% | lift of a generalized quadrangle | — |
| (13, 6) | 374,452 | **388,972** | +3.9% | finite geometry | — |
| (13, 7) | 1,062,936 | **1,064,472** | +0.1% | hexagon cover + hub vertices | — |
| (13, 8) | 5,314,680 | **6,999,552** | +31.7% | finite geometry | — |
| (13, 9) | 50,990,610 | **67,742,688** | +32.9% | orbit search (Haar) | — |
| (13, 10) | 617,330,936 | **683,943,456** | +10.8% | orbit search (Haar) | — |
| (14, 5) | 14,760 | **17,568** | +19.0% | generalized quadrangle construction | — |
| (14, 7) | 1,771,560 | **1,802,642** | +1.8% | hexagon cover + hub vertices | — |
| (14, 9) | 95,087,738 | **120,043,728** | +26.2% | orbit search (Haar) | — |
| (14, 10) | 1,213,477,190 | **1,350,537,864** | +11.3% | orbit search (Haar) | — |
| (15, 3) | 374 | **376** | +0.5% | finite geometry | ✓ |
| (15, 4) | 4,946 | **5,070** | +2.5% | finite geometry | ✓ |
| (15, 6) | 842,048 | **870,440** | +3.4% | finite geometry | — |
| (15, 7) | 2,480,184 | **2,512,488** | +1.3% | hexagon cover + hub vertices | — |
| (15, 8) | 14,172,480 | **18,666,480** | +31.7% | orbit search (Haar) | — |
| (15, 9) | 168,016,334 | **208,483,200** | +24.1% | orbit search (Haar) | — |
| (15, 10) | 2,300,326,510 | **2,566,531,440** | +11.6% | orbit search (Haar) | — |
| (16, 3) | 394 | **396** | +0.5% | finite geometry | ✓ |
| (16, 4) | 5,134 | **5,440** | +6.0% | orbit search (Haar) | ✓ |
| (16, 5) ² | 27,300 | **33,792** | +23.8% | route-chart lift | — |
| (16, 6) | 884,062 | **940,846** | +6.4% | finite geometry | — |
| (16, 7) | 4,022,340 | **4,081,410** | +1.5% | hexagon cover + hub vertices | — |
| (16, 9) | 288,939,118 | **348,207,600** | +20.5% | orbit search (Haar) | — |
| (16, 10) | 4,119,507,330 | **4,708,566,360** | +14.3% | orbit search (Haar) | — |

¹ (10, 8): the table's 1,176,480 is Gómez's ΩH_q (see below). This record was found on 16 November and compared with the table only;
files in [`records/bipartite_dd/d10D8/`](records/bipartite_dd/d10D8/).
² (3, 8): 288 against 256 is a large jump for a well-studied cell; the literature check found nothing published above 256.
(16, 5): beats the table's 27,300, the best published graph (31,460, Cames van Batenburg–Korsky, 2026) and a double cover of
LANL's (16, 4) graph (32,768).

Beyond the table, 94 more cells have a record: Δ = 3 from D = 11 up to D = 39 (2,144,872,686 vertices at D = 39), Δ = 4 to 8 at
D = 11 up to 22, 18, 16, 14 and 13, Δ = 9 to 16 at D = 11, 12 (and (9, 14)), and Δ = 17 to 20 at D ≤ 10 (30,518,778,360 vertices at (20, 10), the
largest). All are in [`records/RECORDS.csv`](records/RECORDS.csv), with date found and literature status. Few of these cells have a published
value to compare with.

### Caveats: what has been checked against the literature

A literature check on 1 November 2026 compared 121 record cells with the live wiki, arXiv, journals and preprints, theses and graph
censuses. Of the cells counted here, **117 hold** (73 table cells and 44 beyond): no larger published bipartite graph was found.
Not covered by that check: (6, 5) and 48 beyond-table cells found after it closed or missed by it, marked `not_yet_checked` in the CSV, and
(10, 8), compared with the table only. So some of these cells may have been improved elsewhere. In detail:

- **Withdrawn:** (15, 5), where we had 20,736 (later 24,624), and (3, 14), where we had 5,706, are **not** claimed. Larger bipartite graphs
  are published: 27,216 at (15, 5) by D. Yugeswardeenoo (Zenodo, 24 Oct 2026, doi:10.5281/zenodo.23624118), and 6,272 at (3, 14) in
  the Foster census of cubic edge-transitive graphs (Conder–Potočnik, J. Algebra 2026). We rebuilt and checked both.
- **Disputed:** (19, 8), 92,599,320, and (20, 8), 131,610,120. No valid published graph beats ours, but Gómez's 1986 construction ΩH_q
  would claim more at those cells if taken at face value. [Our note](papers/Ozden_OmegaH_D8_note.pdf) shows that ΩH_q as defined has
  diameter at least 9, so the doubt is about the 1986 construction, not about our graphs; both cells are marked `contested`. The same
  question also touches the table's own D = 8 values: the 1,176,480 at (10, 8) is an ΩH_q value too, and our audit found that graph has diameter 9.
- **Close calls** (ahead of the best published value by under 1%): (11, 3), (13, 3), (15, 3), (16, 3), (5, 7), (7, 7), (9, 7), (10, 7),
  (13, 7), (11, 8) and, beyond the table, (19, 3) and (19, 5). All are real wins, and the cells where a newly found paper would matter most.

## General-graph records

Cayley graphs of semidirect products, found on 20–21 November 2026. The first four (found 20 November) are Z_m ⋊ Z_n, checked by
two independent BFS programs (numpy and plain Python), each of which builds the group from its definition. The other five (21 November) use
non-metabelian groups F_p² ⋊ Q with Q = Z_k ⋊ Z₂ inside GL(2, p) (product (u, v)(x, y) = (ux, ρ(x)⁻¹v + y)) and were checked three ways:
a bitset BFS, an explicit C BFS and a from-scratch Python or numpy BFS with explicit matrix arithmetic. Every graph has the stated degree and
diameter. "Previous" is the value in Comellas's table, fetched the day the record was found.

| (Δ, D) | Previous | Ours | Group | Layer sizes from one vertex (the graph is vertex-transitive) |
|---|---:|---:|---|---|
| (7, 9) | 1,332,774 | **1,338,558** | F₁₃₁² ⋊ (Z₃₉ ⋊ Z₂) | 1, 7, 42, 252, 1512, 9046, 53161, 279871, 772421, 222245 |
| (7, 10) | 6,645,690 | **6,692,790** | F₁₃₁² ⋊ (Z₁₉₅ ⋊ Z₂) | 1, 7, 42, 252, 1512, 9057, 54020, 313965, 1587575, 3883419, 842940 |
| (8, 7) | 139,867 | **139,965** | Z₁₃₃₃ ⋊ Z₁₀₅ | 1, 8, 56, 392, 2736, 18186, 76938, 41648 |
| (8, 10) | 27,019,307 | **27,036,394** | F₄₁₉² ⋊ (Z₇₇ ⋊ Z₂) | 1, 8, 56, 392, 2744, 19198, 134092, 921239, 5629482, 16660144, 3669038 |
| (9, 10) | 89,658,816 | **90,493,830** | F₃₇₉² ⋊ (Z₃₁₅ ⋊ Z₂) | 1, 9, 72, 576, 4608, 36859, 294284, 2318622, 16508519, 57814857, 13515423 |
| (10, 7) | 625,464 | **625,733** | Z₂₁₅₇₇ ⋊ Z₂₉ | 1, 10, 90, 810, 7268, 62236, 343702, 211616 |
| (10, 8) | 4,524,979 | **4,538,823** | Z₃₆₉₀₁ ⋊ Z₁₂₃ | 1, 10, 90, 810, 7290, 65192, 546590, 2712218, 1206622 |
| (10, 9) | 34,913,494 | **34,934,046** | Z₃₀₆₄₃₉ ⋊ Z₁₁₄ | 1, 10, 90, 810, 7290, 65526, 584374, 4836060, 21928806, 7511079 |
| (12, 8) | 19,218,539 | **19,240,407** | Z₁₁₂₅₁₇ ⋊ Z₁₇₁ | 1, 12, 132, 1452, 15972, 175060, 1825758, 11536300, 5685720 |

Each graph is specified in [`records/general_dd/`](records/general_dd/) by a short witness file (the group, the generators), with its
SHA-256, the check programs (including the C BFS) and their outputs; for the F_p² ⋊ Q graphs the folder also has the small group file and `build_q.py`. These are not bipartite and say nothing about the bipartite table above.

## Verify a record

```bash
python -m venv .venv && .venv/bin/pip install numpy networkx pytest

# a bipartite record graph (edge list as JSON), with three independent checkers: bitsets, networkx, BFS from every vertex
.venv/bin/python scripts/verify_record.py records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json 7 4

# a general-graph record: rebuild the Cayley graph from its witness file and run a BFS (pure Python, about a second)
python3 records/general_dd/check/independent_bfs.py records/general_dd/d8D7/d8D7_N139965.txt
# an F_p² ⋊ Q record, here (7, 9): explicit C BFS on the group file (arguments: file, degree, |Q|, then level v_row v_col per generator; the last triple is the involution)
cc -O2 -o /tmp/bfs_g records/general_dd/d7D9/bfs_g.c && /tmp/bfs_g records/general_dd/d7D9/group_F131sq_Z39_Z2.bin 7 78  7 9 56  13 10 112  57 29 63  2 0 68
# the same graph with the numpy checker (arguments: m n r D then the generators u v, ...)
python3 records/general_dd/check/verify_mc.py 1333 105 855 7  5 398  53 1317  80 668  96 1108

# a Haar-graph record, here (6, 7) with 8,880 vertices: build the edge list, then an all-pairs BFS that assumes no symmetry
python3 research/frontier/build_haar2.py research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt /tmp/edges.txt
cc -O2 -o apsp research/lifts/coordinator_check/apsp.c && ./apsp /tmp/edges.txt 6 7

# the (10, 8) bipartite record (1,185,408 vertices): generate, then BFS from both sides and 400 random sources
cd records/bipartite_dd/d10D8 && python3 gen.py row /tmp/d10D8.bin && cc -O2 -fopenmp -o /tmp/bfs bfs.c && /tmp/bfs /tmp/d10D8.bin 400

# the tests, and the Lean proofs (needs elan; downloads Mathlib's cache)
.venv/bin/python -m pytest -q
cd lean && lake exe cache get && lake build
```

How each kind of record is checked:

- **Haar graphs** (`research/frontier/sols/*.txt`): `research/frontier/build_haar2.py` and the independent `check_haar_indep.py`.
  Above about 20 million vertices, two separately written low-memory C checkers (`haarcheck_sl.c` / `haarcheck_psl.c` and `bigcheck_indep.c`);
  reports are in `research/frontier/runs/cloudcheck/`.
- **Other graphs** (lifts, geometry, hexagon, route charts): rebuilt from their builder, then checked by an all-pairs BFS that
  assumes no symmetry ([`apsp.c`](research/lifts/coordinator_check/apsp.c)). Each also fails, as it should, when the diameter limit
  is lowered by one. Logs: `research/coordinator_check/`, `research/lifts/coordinator_check/`, `research/theorems/coordinator_check/`,
  `research/squads/exp2/coordinator_check/`.
- **The first eight records** also passed three independent checkers (bitsets, networkx, and a from-scratch BFS from every vertex).

Graph files and builders for the earlier records are in the repository (index: [`research/RESULTS.md`](research/RESULTS.md)), as are those for (10, 8)
and the general records. The 38 beyond-table records found on 17–19 November (D up to 39, mostly Δ = 3–5) are listed in the CSV and not yet published here.

## Checked in Lean

`lean/` is a Lean 4 + Mathlib project. Each record theorem has the form `∃ G : SimpleGraph (Fin n), IsBipartiteDegDiam G Δ D`.

- [`lean/BipartiteDD/Records.lean`](lean/BipartiteDD/Records.lean) proves the first eight records, by a checker proved sound once and
  run in the kernel (`decide +kernel`, no `native_decide`).
- [`lean/BipartiteDD/Haar/`](lean/BipartiteDD/Haar/) proves the larger Haar and lift records. A general lemma reduces the diameter of a
  Haar graph to a covering condition in the group, which kernel-checked certificates then verify. Notes: [`research/lean-haarD/`](research/lean-haarD/).
- [`lean/BipartiteDD/Plus2/`](lean/BipartiteDD/Plus2/) proves the +2 theorem (below) for every finite projective plane.

Every theorem's `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound` (`Axioms.out.txt` files next to the proofs).
No `sorry`, `admit` or `native_decide`. Most of the larger graphs are too big for kernel-checked certificates and are checked by BFS only.

## The +2 theorem

> For every finite projective plane of order q ≥ 4 there is a bipartite graph with 2(q² + q + 6) vertices, maximum degree q + 2 and diameter 3.

Araujo-Pardo and López (2022) built such graphs with 2(q² + q + 5) vertices and asked readers to improve the construction.
The search found graphs exactly 2 larger at q = 9, 11 and 13. All three add a fourth "hat" pair (a copy of a point and a copy of a line)
and rotate three incidences to make room. The general rule, its proof and computer checks are in
[`research/plus2/REPORT.md`](research/plus2/REPORT.md); a short note for mathematicians is in [`research/plus2/note/`](research/plus2/note/).

## The constructions

- **Program search** ([`evolve/`](evolve/)): an evolutionary search over graph-building programs, in the spirit of Google DeepMind's
  [AlphaEvolve](https://arxiv.org/abs/2506.13131). It found the first records, at D = 3, 4 and 5.
- **Finite geometry** ([`research/plus2/`](research/plus2/), [`research/geometry/`](research/geometry/), [`research/p4/`](research/p4/)):
  constructions on projective planes, generalized quadrangles and hexagons: the +2 theorem, "hats" and "whiskers", and the D = 3, 4 and 6 cells.
- **Haar graphs** ([`research/frontier/`](research/frontier/)): a Haar graph is built from a group G and a set S of Δ elements; the diameter is
  checked by a bitset BFS. A measured size law (`SIZE_LAW.md`) explains where random choices of S stop working.
- **Orbit search** ([`research/structured/`](research/structured/), theory in [`research/theory/`](research/theory/)): S closed under a group
  automorphism. This raised most D = 7–10 cells.
- **Voltage lifts and metacyclic Haar graphs** ([`research/lifts/`](research/lifts/)): the small-degree cells (Δ = 3–5, D = 7–10).
- **Route-chart lifts** ([`research/theorems/`](research/theorems/)): lifts of a small controller graph whose edges carry "chart letters" over a
  finite field. These gave (16, 5), (8, 5), (12, 5) and (15, 5) (the last since overtaken by a published graph).
- **Generalized quadrangles at D = 5** ([`research/d10D7/DM_D5.md`](research/d10D7/DM_D5.md)): (10, 5), (11, 5), (12, 5) and (14, 5), about 20% above the table.
- **Hexagon + hub vertices** ([`research/squads/exp2/hexd7/`](research/squads/exp2/hexd7/)): the table's D = 7 values are three copies of a
  generalized hexagon H(q). Freeing a point–line pair and adding two hub vertices gains 2 vertices per pair, with a short proof.
  This gave (7, 7), (9, 7) and (11, 7).
- **Cayley graphs of Z_m ⋊ Z_n** ([`records/general_dd/`](records/general_dd/)): the nine general-graph records.

## Layout

| Path | What it is |
|---|---|
| `records/RECORDS.csv` | every bipartite record: cell, table value, ours, date found, literature status |
| `records/general_dd/` | the nine general-graph records, witness files, checkers and check outputs |
| `records/bipartite_dd/` | record graphs with their builders: the first eight, (6, 5), (10, 8), and the literature check of the first eight |
| `research/frontier/` | Haar graph search, size law, solution files (`sols/`), checkers, check reports |
| `research/structured/`, `research/theory/`, `research/theorems/` | orbit search and its theory; route-chart lifts, flag graphs |
| `research/lifts/` | voltage lifts and metacyclic Haar graphs |
| `research/plus2/`, `research/geometry/`, `research/p4/`, `research/squads/` | finite-geometry constructions and proofs, including the D = 7 hexagon construction |
| `research/lean-haarD/`, `lean/` | Lean notes and proofs |
| `papers/` | the notes for readers (PDF) |
| `evolve/`, `problems/bipartite_dd/`, `configs/` | the program search and its problem definition |
| `scripts/`, `tools/`, `tests/` | verification and helpers |

## Credits

Doğa Özden and Claude

Prior work: the table's authors and the Combinatorics Wiki's maintainers, whose published values and constructions are the baseline
throughout, notably Delorme, Gómez, Farhi, Hafner, Loz, Pérez-Rosés, Pineda-Villavicencio, Feria-Purón, Miller, Araujo-Pardo and López.

## License

Code (`evolve/`, `problems/`, `scripts/`, `tests/`, `lean/`) is under the [MIT License](LICENSE). The record graphs, run logs, research
write-ups, pages and documents are under [CC BY 4.0](LICENSE-DATA): reuse them freely, with credit.
