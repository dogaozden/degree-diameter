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
- **q=5, Z14 (Delta = 8, 2N*m = 109,368 vertices): diameter 8, verified.** Annealed with hexeval (full cost, random
  start, 491 iterations to far-cost 0). The first solution had ONE parallel edge (a matching edge p-sigma(p) lying on a
  hexagon line with the same voltage, giving 14 double edges per side in the lift). Fixed by `FIXDUP=1` (try all
  voltages of that matching edge; cost 0, no parallel edges). Saved as runs/q5_m14_fix.sol. Independent BFS check
  (src/indep.c: explicit lift graph, BFS from all 2N base vertices in copy 0): simple, 8-regular, diameter 8,
  far pairs 0: DIAMETER_OK. 13 was the previous formula-based best at q=5 (Plücker pencil, D8_COMPOUND 4.7).
- q=5, Z16 annealed from random (full cost, about 1 s per evaluation): 208 iterations, cost 30; too slow, stopped
  (runs/q5_m16_hx.log). The Z14 start was at cost 4 and reached 0 in 491 steps: the difficulty rises fast from m=14 to 16.
- Structure check of the verified Z14 lift: every hexagon and matching voltage is spread uniformly over Z14 (no visible
  pattern). The annealed lifts are unstructured. No formula was found.
- **q=5, Z15 (Delta = 8, 117,180 vertices): diameter 8, verified** (runs/q5_m15_hx2.sol; indep.c DIAMETER_OK, simple).
  Path: random start (cost 16 after FIXDUP), 900 annealing steps to cost 1, then 23 steps at T0 = 0.4 to 0.
  Z15 is the new q=5 best (formula-free). Z16: stalled (cost 30 after 208 steps).
- **q=4, Z20 (Delta = 7, 54,600 vertices): diameter 8, verified** (runs/q4_m20_hx2.sol; indep DIAMETER_OK, simple).
  Path: random start, 1,500 steps to cost 4, then 621 steps at T0 = 0.3 to 0. This equals the table multiplier
  5*floor((q+5)/2) = 20 at q = 4.
- **q=3, Z24 (Delta = 6, 17,472 vertices): diameter 8, verified** (runs/q3_m24_hx.sol; indep DIAMETER_OK). Found in
  2,133 steps from a random start with FIXDUP. (The earlier lift3 run at Z24 had stalled at cost 8 in 5 minutes.)

## Result table (verified = src/indep.c explicit BFS over all 2N base sources, DIAMETER_OK, simple graph)

| q | Delta = q+3 | copies m (cyclic Z_m) | vertices 2Nm | verified | how found |
|---|---|---|---|---|---|
| 3 | 6 | 24 | 17,472 | yes | annealed (hexeval, 2,133 steps from random); Z28 stalls at cost 12 after 8,000 steps |
| 4 | 7 | 20 | 54,600 | yes | annealed (1,500 + 621 steps); equals the table multiplier 5*floor((q+5)/2) = 20 |
| 5 | 8 | 15 (14 also) | 117,180 (109,368) | yes | annealed; Z16 stalls at cost 30 after 208 steps |
| 7 | 10 | not reached | - | - | lab's annealed best is 17; one q=7 evaluation takes about 1 min here |
| 8 | 10 (1 matching) | not attempted | - | - | one q=8 evaluation is about 60 s with hexeval |

Comparison with the table multiplier 5*floor((q+5)/2): q=3 table 20 (we have 24), q=4 table 20 (we have 20),
q=5 table 25 (we have 15; the formula-based Plucker pencil design had 13).

## Analysis

- The annealed lifts are unstructured (voltages uniform over Z_m). No formula was found, and no voltage design
  defined for every q was built or verified. The trivial-hexagon-voltage family is capped for guaranteed walks at
  m <= 2q+11+2 sqrt(2q+9) (D8_COMPOUND Thm 2.3): 24.7 at q=3, 29.7 at q=5, 34.6 at q=7.
- Random lifts are much closer to valid than the notes said: at q=5, random Z13/Z14/Z15 starts often have far cost
  0-7 before annealing; the difficulty grows sharply between m=14 and m=16 (q=5) and between 24 and 28 (q=3).
- Parallel edges are a real issue for annealing: a matching edge p-sigma(p) on a hexagon line with an equal voltage
  gives a double edge. The annealer's random moves rarely fix it, so hexeval has a penalty (100 per double edge) and
  a targeted repair (FIXDUP=1: try all voltages of each affected matching edge).
- lift3 with SRC sampling reports cost 0 on sampled sources while the full check is positive (Z14, q=5, cost 10): do
  not use SRC sampling for claims.

## Next (not done)

- Use hexeval's FIXDUP and penalty at q=7 with m=17..20 and a faster full evaluation (point sources only, 7 steps,
  done; still about 1 min per evaluation), or restrict voltages to a formula class and anneal over the class values.
- Structured candidates to test next: the Z_5 x (squares of GF(q)*) guess from REGULARITIES.md 2.1 (group order
  5*((q-1)/2+3)); a multiplicative coordinate on H(q) is needed first.

## Files

- src/hexgen2.c, src/hexcheck.c, src/lift3.c (copies from research/d10D8/hex); src/hexeval.c (point-source evaluator,
  cyclic groups, FIXDUP, parallel-edge penalty); src/indep.c (independent explicit-graph BFS checker).
- runs/*.sol: solution files in lift3 format (the verified ones: q3_m24_hx.sol, q4_m20_hx2.sol, q5_m14_fix.sol,
  q5_m15_hx2.sol; q3_cyc22_a.sol is the Z22 lift, also verified).
- Scoreboard lines (scoreboard.tsv): q=3 Z22, q=5 Z14, q=5 Z15, q=4 Z20, q=3 Z24 (all Delta < 10, not the target cell).
