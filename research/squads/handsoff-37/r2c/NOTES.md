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
