# (3,7) exact: tools for job exact-3-7 (Oct 27, 2026)

Notes and results: `research/squads/cells/d3D7_exact.md`.

| file | what it does |
|---|---|
| `zplift.c` | exhaustive Z_p voltage lifts of every cubic bipartite base multigraph (nauty multig -T format on stdin), keeps lifts of diameter <= D; walks are linear forms in the cotree voltages; collision pruning; `-brute` turns pruning off |
| `glift.c` | the same for arbitrary groups (tables from `gap_groups.g`); walks are freely reduced words; first non-identity voltage is an Aut(G)-orbit representative |
| `jsearch.c` | Z_p version that builds base and voltages together (bases too large to list); env `SHARD=i/m SHARDDEPTH=d` splits the search, env `PROBE=N` gives a Knuth estimate of the tree size |
| `crosscheck.py`, `crosscheck_g.py` | independent brute force (own spanning tree, every assignment, BFS diameter) for validating zplift / glift |
| `compare_iso.py` | compares zplift and jsearch solution sets up to isomorphism (nauty labelg) |
| `liftedges.py`, `gliftedges.py` | edge list of a zplift / glift solution (check with `bin/apsp EDGES 3 7`) |
| `test_delta3.py` | checks the n = 248 structure theorem (notes §2.6) in its general-D form on real graphs (D = 5, n = 56) |
| `gap_groups.g` | exports SmallGroups (multiplication table + Aut-orbit representatives) to `groups/g<N>.txt` (not committed; `groups/k<K>.txt`, `groups/p<K>.txt` are concatenations, see `runs/gl/`) |
| `bases/bK.txt` | all connected cubic bipartite multigraphs on K+K vertices: `nauty-genbg -cq -d1:1 -D3:3 K K \| nauty-multig -q -r3 -m3 -T` (1, 3, 6, 16, 59, 243, 1,207 for K = 2..8; K = 9, 10, 11 give 6,979, 45,687 and 335,178 and are regenerated with the same command, not committed); `b1.txt` is the Haar base |
| `runs/` | `run_small.sh`, `run_mid.sh` and `zp_p*_k*.out` (zplift), `gl/` (glift), `js/` (jsearch shards), `val/` (validations) |

Build: `mkdir -p bin; for t in zplift glift jsearch; do gcc -O3 -march=native -o bin/$t $t.c -lm; done;
gcc -O2 -o bin/apsp ../lifts/coordinator_check/apsp.c`. Needs `apt-get install nauty gap gap-smallgrp` and
`pip install networkx` for the Python checks. (The runs used binaries named `glift_fix` = glift.c as committed, and
`jsearch3` = jsearch.c as committed.)

Reproduce the main negative results:
- `bin/zplift 13 7 < bases/b7.txt` and the lists in `runs/run_small.sh`, `runs/run_mid.sh` (p >= 11).
- `bin/glift groups/k5.txt 7 < bases/b5.txt` etc. (`runs/gl/run_gl.sh K`), after `echo 'ords:=[...];; Read("gap_groups.g");' | gap -q`.
- `SHARD=i/8 SHARDDEPTH=24 bin/jsearch 7 17 7` for i = 0..7 (order 7, n = 238), `runs/js/run_shard.sh`.
