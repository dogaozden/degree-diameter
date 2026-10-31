# handsoff-65 shared tools (copied from branch claude/squad-6-5-rounds-ts5nxk, research/s65/tools + tabu; all compiled here)

Read the header comment of a .c file for its exact usage. Binaries are already built in this folder (gcc -O3).

| tool | what it does |
|---|---|
| `check.sh EDGES` | scorer for ANY graph: prints `SCORE n=.. maxdeg=.. bipartite=.. bad=<pairs at distance > 5>`; runs apsp_ref when bad=0 |
| `score65 EDGES` | the scorer alone (bit-parallel BFS). Edge list format: first number n, then lines "u v", 0-based |
| `apsp_ref EDGES 6 5` | the coordinator's all-pairs checker (copy of research/lifts/coordinator_check/apsp.c) |
| `vl BASE GROUP` | simulated annealing over voltage lifts of a small bipartite base multigraph by a group (vl format) |
| `tabu SOL GROUP [OUT]` | tabu search over single-voltage changes of a lift; the best lift tool (finds the 684 Haar graph in 0.9 s) |
| `kdesc`, `kopt` | exact steepest descent / exact k-opt over voltage changes of a lift |
| `mcos` | annealer for multi-orbit coset graphs: TYPE "1|1" = Haar, "2|2" = bi-coset, "1|2,2", "2,2|2,2", "1|3,3,3", ... |
| `dcenum FILE.dc 6` | exhaustive unions of double cosets for bi-coset graphs B(G;H,K) exported by `dc_export.g` / `bicoset.g` |
| `bicoset` | exhaustive scan of unions of L-orbits (bi-coset graphs, from fresh-6-5) |
| `haarex3` | exhaustive Haar search H(G,S), |S| = 6 (all groups 343-400 except 384 are already closed: do not redo) |
| `bicay` | bi-Cayley graphs annealer |
| `export_lift.py`, `verify_lift.py`, `haar2lift.py`, `normlift.py` | lift <-> edge-list helpers |
| `gap_tables.g`, `tables.g` | GAP: multiplication tables of SmallGroups (element 0 = identity): `gap -q -c 'ORDER:=176; OUTDIR:="tabs";' gap_tables.g` |
| `near704_c11q16.edges` | the closest graph above 684 known: a 704-vertex lift by C11:Q16 = SmallGroup(176,17), bad = 352 pairs |

GAP 4.12 with the SmallGroups library is installed (`gap -q`). Python 3 has no numpy/networkx; write C for anything heavy.
Prior results (do not repeat): every degree-6 Haar graph on 686-800 vertices is closed except 768 (another job sweeps
768 Haar graphs: leave them out). Bi-coset |H|=|K|=2 at |G| = 686-720: best 8. 2+2 lifts at 704-720: tabu cost 4-6.
3+3 lifts: 14 at 696. bi-Cayley: 4 at 704. "1|2,2": 27. Vertex deletion + rewiring of near misses: 1428 bad pairs at 686.
