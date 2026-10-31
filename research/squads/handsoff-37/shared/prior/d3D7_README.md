# (Δ, D) = (3, 7): tools (job new-3-7, Oct 26 2026)

Goal: a cubic (max degree 3) bipartite graph with diameter ≤ 7 on ≥ 170 vertices. Table: 168 (Conder–Nedela / DGQ / Loz).
Bipartite Moore bound: 254. A cubic bipartite graph has diameter ≤ 7 iff every two vertices on the same side are at
distance ≤ 6. Notes and results: `research/squads/cells/d3D7.md`.

Build: `mkdir -p bin && for t in liftx sa3 salift; do gcc -O3 -march=native -o bin/$t $t.c -lm; done;
gcc -O2 -o bin/apsp ../lifts/coordinator_check/apsp.c`. Groups: `apt-get install gap gap-smallgrp`, then
`echo 'lo:=2;; hi:=127;; Read("gap_export.g");' | gap -q -o 4g` (and `gap_aut.g` for Aut orbit representatives);
the tables go to `groups/` (not committed, ~20 MB).

| tool | what it does |
|---|---|
| `gap_export.g`, `gap_aut.g` | every SmallGroup of order lo..hi as a multiplication table (identity = 0); Aut(G) orbit representatives |
| `liftx BASE GROUPS D [id..]` | exhaustive voltage lifts of a base multigraph over every group in a table file (env AUT = orbit reps file) |
| `enum_bases.py p DIR` | all connected cubic bipartite p+p base multigraphs up to isomorphism (p = 2..5: 1, 3, 6, 15) |
| `salift p GROUPS id seed secs [T0 T1 out.sol]` | annealing over base graph AND voltages jointly; cost = #(base vertex, vertex) pairs at distance > 7 |
| `sa3 n seed secs [T0 T1 init.edges out.edges]` | annealing over unstructured cubic bipartite graphs (edge switches), bit-parallel all-pairs cost (~5 µs at n = 170) |
| `liftedges.py BASE GROUPS id v1..vE` | edge list of a liftx solution (vertex (u,g) = uN+g, edge (u,g) ~ (v, g·a)) |
| `cvt_scan.py ZIP lo hi D` | scan of the cubic vertex-transitive census (graphsym.net, Census3valentVT.zip) |
| `bin/apsp EDGES 3 7` | the repo's independent all-pairs checker (research/lifts/coordinator_check/apsp.c) |
| `seeds/conder168.edges` | the table graph, rebuilt as a lift of the 2+2 base over C2 × (C7 ⋊ C3) = SmallGroup(42,2) |

Edge-list format: first line n, then one "u v" per edge (0-based).
