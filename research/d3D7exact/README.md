# (3,7) exact: tools for job exact-3-7 (Oct 27, 2026)

Notes and results: `research/squads/cells/d3D7_exact.md`.

| file | what it does |
|---|---|
| `zplift.c` | exhaustive Z_p voltage lifts of every cubic bipartite base multigraph (nauty multig -T format), keeps lifts of diameter <= D; collision pruning; `-brute` turns pruning off |
| `crosscheck.py` | independent count (own DFS spanning tree, plain BFS diameter of every lift) to validate zplift |
| `liftedges.py` | edge list of a zplift solution |
| `bases/bK.txt` | all connected cubic bipartite multigraphs on K+K vertices: `nauty-genbg -cq -d1:1 -D3:3 K K \| nauty-multig -q -r3 -m3 -T` (K = 8: 1,207; K = 9: 6,979 and K = 10: 45,687 are regenerated with the same command, not committed) |
| `runs/` | outputs; `run_small.sh`, `run_mid.sh` |

Build: `gcc -O3 -march=native -o bin/zplift zplift.c; gcc -O2 -o bin/apsp ../lifts/coordinator_check/apsp.c`.
