# c6-hexagon: voltage lifts of H(q) + 2 matchings (worker c6, squad handsoff-108)

Folder: research/squads/handsoff-108/c6-hexagon/. Tools copied from research/d10D8/hex/ (hexgen2.c, hexcheck.c,
lift3.c) into src/ and built there. hex/ holds H(3), H(4), H(5) (`src/hexgen2 q`).
Evaluator: `GROUP="cyc m" J=2 D=8 IN=<sol> ITERS=0 ./src/lift3 q` prints the initial cost (0 = diameter <= 8).
Check of the evaluator: the cost sums, over all base sources and all base targets, the uncovered sheets within D=8
(walks of length D-1 or D, which covers all lengths <= D by backtracking).

## Log

- Reproduced the ten-level lemma: GROUP="cyc 10", T="1 4", random matchings, zero hexagon voltages: cost 0 at q=3
  (3 seeds) and q=5 (2 seeds). T="1 2" at q=3: cost 10.
- Annealing calibration at q=3 (J=2, Delta = 6, default TEMP0=2, TEMP1=0.05, all sources):
  cyc 20 cost 0 after 37 iterations; cyc 21 cost 0 after 335; cyc 22 cost 0 after 304.
  (Z24 run: best 14 after 1,286 iterations, see below.)
- Z24 at q=3 (full cost, 300 s): best 8 after 2,373 iterations, no cost 0 (timeout).
- Evaluator issue found: lift3 with SRC sampling reports cost 0 on 200-300 sampled sources while the full check is
  10 (Z14, q=5, random start). Use full costs only.
- New evaluator src/hexeval.c (point sources only, walks of length 7; lanes packed; cyclic Z_m). It agrees with lift3:
  zero/nonzero status identical; hexeval cost = lift3 fullcost / 2 (lift3 counts both point->line and line->point
  sides). Its cost unit = uncovered (point p at copy 0, line y, sheet g) triples = far point-line pairs from copy-0
  points. One q=5 full evaluation at m=14: 0.6 s (lift3: 5.7 s).
- Random Z14 at q=5 (hexeval): initial cost 4-5 (units above), i.e. random lifts are close to valid already.
