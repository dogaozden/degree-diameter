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
