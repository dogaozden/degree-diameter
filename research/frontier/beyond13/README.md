# beyond13: job beyond-d13 (2026-11-01)

New cells D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8, plus raises of (4,11), (5,11), (6,11), (4,12), (5,12) and a
(5,10) value above the 2013 table. Results and discussion: research/frontier/beyond/BEYOND_TABLE.md (rows and the section
"D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8"); theory: THEORY.md; squad log: research/squads/LOG.md.

- `cells.txt` — Haar graphs of SL/PSL(2,q) x Z_n: cell | solution stem in sols/ | note. Each has runs/<stem>.gen.txt
  (haarcheck_gen; copies for research/frontier/runs/cloudcheck/). Card-run logs say so in their first line.
- `cells_other.txt` — everything else (metacyclic groups, products, lifts, A6 x Z4): cell | vertices | edge list in
  graphs/ | check file in checks/ | note. The largest VALID entry per cell is the value.
- `rows13.py` (rows for BEYOND_TABLE), `splice13.py` (puts rows and SECTION_D13.md into BEYOND_TABLE.md).
- Checkers: `../haarcheck_gen.c` (SL/PSL), `metacheck.py` (metacyclic Z_m x|_r Z_k x Z_n, own numpy BFS from (e,A) and
  (e,B)), `metacheck2.py` (products of metacyclic groups), `../../lifts/coordinator_check/apsp.c` (all pairs; every
  graph below 5e5 vertices), `meta2edges.py` / `tab2edges.py` (edge lists from solutions / group tables).
- Search tools: `../beyond11/haar_big0.c` (orbit search, bin/haar_big0), `../haar_gen3.c` (random S, many families),
  `meta/hmeta.c` (bit-parallel metacyclic Haar search; random S + targeted moves; START, EVAL, OPT2 = exhaustive
  2-opt), `meta/mpick.py`, `lifts/lift.c` (squad r2/e16), `lifts/liftd.c` (any degree), `lifts/scan_h02.c` (squad
  r5/h02's 1-opt + tabu lift finisher), `lifts/scanchain.sh`, `lifts/lmulti.sh`.
- Build: `gcc -O3 -march=native -fopenmp -o bin/X X.c -lm` (bin/ is not committed).
