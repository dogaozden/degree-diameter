# beyond15: job beyond-d15 (2026-11-01/02)

First values for the new cells D = 15 and D = 16 at Δ = 3..6. Results and discussion: research/frontier/beyond/BEYOND_TABLE.md
(rows and the section "D = 15 and D = 16 at Δ = 3..6"); theory: THEORY15.md; squad log: research/squads/LOG.md
(rounds 1-4 of beyond-d15); cards and scoreboards: research/squads/beyond15/r1..r4.

| D \ Δ | 3 | 4 | 5 | 6 |
|---|---|---|---|---|
| 15 | 12,246 | 1,343,054 | 47,587,354 | 867,831,360 |
| 16 | 20,466 | 3,623,866 | 172,011,046 | 4,021,844,904 |

- `cells.txt` — SL/PSL(2,p) x Z_n Haar graphs: cell | solution stem in sols/ | note (haarcheck_gen log runs/<stem>.gen.txt).
- `cells_other.txt` — everything else: cell | vertices | edge list in ../beyond/graphs/ | check file | note. The largest VALID
  entry per cell is the value. `rows15.py` makes the BEYOND_TABLE rows, `splice15.py` puts rows, SUMMARY_D15.md and
  SECTION_D15.md into BEYOND_TABLE.md (idempotent).
- Checkers: `../haarcheck_gen.c` (SL/PSL x Z_n), `metacheck.c` (metacyclic groups and products, any N to ~1e9; own group
  code, bitset BFS from (e,A) and (e,B); agrees level by level with ../beyond13/metacheck.py), `../../lifts/coordinator_check/apsp.c`
  (all pairs; every cubic graph). `check_one.sh` logs command, sha256 of inputs, output, exit code and times; `savegraph.sh`
  gzips an edge list into ../beyond/graphs/ and runs apsp into ../beyond/checks/.
- Searches: `../beyond11/haar_big0.c` (Δ = 6, alpha-orbit S), `../beyond13/meta/hmeta.c` (metacyclic groups, random S),
  `liftsym.c` (symmetric voltage lifts; anneal, or EXH = exhaustive over gauge classes, with a CRT product for composite
  squarefree n), `lsym/` (bases with rotations: mklcf.py; sweep.py over n; haarsweep.py = all cubic metacyclic Haar graphs;
  quotsweep.py = 4-orbit quotient; quotgen.py = any quotient multigraph; logs in lsym/logs/), `closer.sh` (chains hmeta links
  with new seeds from a saved cost-2 state), `hq.sh` / `gen.sh` (Δ = 6 search + check).
- Build: `gcc -O3 -march=native -fopenmp -o ../bin/X X.c -lm` (../bin/ is not committed).
- Rebuild a cubic graph: the voltages (.best, "edge voltage" lines) and the base (.base.txt/.perm or lsym/<name>.txt/.perm)
  are next to the edge list in ../beyond/graphs/; `liftsym BASE PERM n lambda D 0 1 OUT` with START=<.best> rewrites OUT.edges
  when the cost is 0.
