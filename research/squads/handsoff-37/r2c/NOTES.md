# r2c NOTES: polarity covers, deeper (card r2c, continues c6)

Start: 2026-10-31T17:25:25Z (date -u). Stop about 19:40Z (at least 2 h).

## Plan
Extend the c6 model (c6/lift.c: zero loops only, free Z_t) with the moves c6 never had:
- 2-stub loops with voltage g (M-edges (u,x)~(u,x+g), 2g != 0 mod t) and 1-stub loops (2g = 0);
- an optional fixed vertex f of M (hub): orbit hu is joined to f (needs t = 3, 85 = 3*28 + 1).
Engine: lift2.c (SA over stub items; moves are stub-preserving: volt, 2-switch, split/combine loops,
1-stub slide, pair/unpair 1-stub loops, hub slide). Calibrate first (m = 80 Z5 must reach 0), then m = 85.
Cost as in c6: unordered pairs {i,j} of M with no even walk of length <= 6; far = 2 * cost.

## 17:40Z calibration (lift2 = extended model; far = 2 * cost; all checked with bin/score37)
- m=80 (n=160), k=16, t=5, H=0: zero cost in 13 s (seed 2, T 1.5 -> 0.2, 2M iters per restart); seed 3 also zero.
  Verified: score37 far=0 diam=7, apsp RESULT VALID (out/t80b_best.edges). The old zero-loop-only SA (c6) needed 70 s.
  Lower temperatures (T 5 -> 0.3) floor at cost 30 in 40 s: temperature matters, deltas are multiples of ~1 here.
- m=85 (n=170), k=17, t=5, H=0: 500 s run started (out/t85a_*). Result below when it finishes.
- m=85 (n=170), k=17, t=5, H=0, lift2 (2-stub loops + 1-stub loops + 2-switch): 500 s, floor cost 40 (far 80), the same
  floor as c6's zero-loop model. So the extra loop types do not lower the Z5 floor at m=85. Not logged (not below 46).
- Hub model (fixed vertex f of M, Z3 on the other 81 vertices, m = 3k+1): m=82 (k=27, n=164), 240 s: floor cost 27
  (far 54), NOT zero. Hub calibration is weak; the Z3 family with 27 orbits is hard (c6's old model gave 66 at m=84).
  m=85 hub (n=170) is not promising from this calibration; parked.
- Next: the board is weak at n = 172 (76), 174 (107), 176 (122). Polarity covers at m = 86, 87, 88 can lower these:
  calibrate m=88 (Z4, k=22) and m=87 (Z3, k=29) with 240 s runs.
- m=88 (n=176), Z4 k=22 (lift2), 240 s: floor cost 90 (far 180). Much worse than m=85 Z5 (40): the Z4 base is harder
  (temperatures were tuned for Z5). Not competitive with the board's 122 at 176 (c1); kept only as a calibration row.
- m=87 (n=174), Z3 k=29 (lift2), 240 s, T 1.5 -> 0.2: cost 72 (far 144), still falling. Cost moves come in units of t,
  so T should scale with t (T = 0.3 t for the Z5 runs that worked). Re-running with T scaled by t.
- m=87 (n=174), Z3 k=29, T scaled to t (2.7 -> 0.36), 5M iters, 240 s: cost 69 (far 138). Z3 with 29 orbits is a weak
  family in this SA (c6's (28,3) at m=84 gave 66 too). Z5 is the only family here that reaches low cost.
- m=86 (n=172), Z2 k=43 (lift2), 240 s, T 1.0 -> 0.15, 5M iters: floor 81 (far 162). Z2 SA is weak here (c6's tabu
  reached cost 38 once at m=86, see c6/NOTES.md). n=170 lift2 graph saved: r2c/best170_lift2_far80.edges (far 80).
- Next: iterated local search (restart from the best base with 6 random moves, reheat 0.4 -> 0.1) at m=86 for 540 s.
- m=86 ILS (540 s, pert 6, reheat 0.4 -> 0.1) from the best base: 74 (far 148). Weak; the Z2 family does not compete.
- Hub at m=85 (n=170, k=28, H=1, Z3 + fixed vertex), T scaled to t=3 (2.7 -> 0.36): the one run that could beat 46.
- Hub at m=85 (n=170, Z3 k=28 + fixed vertex, 300 s, T 2.7 -> 0.36): floor 57 (far 114). Worse than Z5 (40); parked.
- Z5 m=85 ILS (540 s, pert 6 from its own best, reheat 0.6 -> 0.15): floor 45 (far 90). Not below the 40 floor.
- Hub at m=79 (n=158, k=26, Z3 + fixed vertex, 240 s): cost 18 (far 36), not zero. The hub family does not reach zero
  even at n = 158, so it is weaker than Z5 (zero at n = 160 in 13 s). Parked.
- 18:30Z plan for the rest: exact local re-solve (lns.c) of the cost-40 Z5 floor (out/t85a_best.items): free all stubs of
  every 3-subset of base vertices, enumerate every re-completion, score it exactly with the full cost. Tests whether
  the 40 floor is 3-local-optimal.
- Exact local re-solve (lns.c, out/t85a_best.items = cost-40 floor): every 3-subset (680 subsets, 10.6k completions),
  every 4-subset (2380, 613k), every 5-subset of the 17 base vertices (6188 subsets, 64.6M completions, 2.5 min):
  NO completion below cost 40. The Z5 floor at m=85 is 5-base-vertex locally optimal.

## 18:55Z: correction and summary of the second half

- CORRECTION: far = 2*cost is only a lower bound for the cover. For cost > 0 some CROSS pairs (A_i, B_j) can also be at
  distance > 7 (same-side pairs > 6 make the neighbour argument fail). Example: out/m86ils_best (cost 74) has far 150, not 148
  (2 cross pairs at distance 9; python BFS and score37 agree). All far numbers below and in the scoreboard come from
  bin/score37, not from 2*cost.
- Board rows logged (first r2c graph at each n, all checked with bin/score37): 170 far 80 (Z5, r2c/best170_lift2_far80.edges),
  172 far 150 (Z2 ILS, r2c/best172_lift2_far150.edges), 174 far 138 (Z3 k=29, r2c/best174_lift2_far138.edges),
  176 far 180 (Z4 k=22, r2c/best176_lift2_far180.edges), calib n=160 far 0 (r2c/calib160_lift2_zero.edges, apsp VALID).
  None beats the board (170: 46 from c1; 172: 76 from c6; 174: 107 from c1; 176: 122 from c1).

### Results table (lift2 engine, all runs in r2c/out/, cost = same-side bad pairs)
| model | m (n) | run | cost | far (score37) |
| Z5 zero-loop+2-stub, k=16 | 80 (160) | 13 s, T 1.5->0.2 | 0 | 0 (apsp VALID) |
| Z5, k=17 | 85 (170) | 500 s SA | 40 | 80 |
| Z5, k=17 | 85 (170) | 540 s ILS (pert 6) | 45 | 90 |
| Z3 hub, k=28 | 85 (170) | 300 s | 57 | 114 |
| Z3 hub, k=27 | 82 (164) | 240 s | 27 | 54 |
| Z3 hub, k=26 | 79 (158) | 240 s | 18 | 36 |
| Z3, k=29 | 87 (174) | 240 s T 1.5->0.2 | 72 | 144 |
| Z3, k=29 | 87 (174) | 240 s T 2.7->0.36, 5M | 69 | 138 |
| Z4, k=22 | 88 (176) | 240 s T 1.5->0.2 | 90 | 180 |
| Z2, k=43 | 86 (172) | 240 s SA | 81 | 162 |
| Z2, k=43 | 86 (172) | 540 s ILS | 74 | 150 |

### Verdicts
- Extra loop types (2-stub loops, 1-stub loops) do not lower the Z5 floor at m=85: 40 again (c6 model: 40).
- Exact local re-solve (lns.c) on the cost-40 Z5 floor: all 3-subsets (680), 4-subsets (2380), 5-subsets (6188, 64.6M
  completions, 2.5 min) of the 17 base vertices give nothing below 40. 6-subsets of the 10 base vertices that carry the
  40 uncovered pairs: see the log below (out/lns6_pool10.log).
- Fixed-point (hub) Z3 family: floors 57 (m=85), 27 (m=82), 18 (m=79): no zero even at m=79, weaker than Z5.
- Z4 (m=88) and Z3 (m=87) and Z2 (m=86) are weak in this SA; the Z5 family is the only one with zeros at m >= 80.
- Next step if continued: a second symmetry for Z5 (the involution x -> -x fixing the 17 base vertices, i.e. a D5 family),
  which halves the space; the Z5 m=85 floor is the target (needs cost <= 22 to beat far 46 at n=170).
