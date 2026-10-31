# r3a NOTES (worker r3a, round 3, card r3a: non-free symmetric search at n = 170 and 180)

Start: 2026-10-31T18:17Z (date -u). Stop about 20:17-20:32Z (2h to 2h15).

## Setup (18:18-18:21Z)
- Copied r2f/symloc.c (SA over G-invariant cubic bipartite graphs; cost = same-side pairs at distance > 6,
  counted over G-orbit representatives), r2f/mkgroup.py (G = <z,s>, z = Z_M shift, s = (sigma_A, sigma_B; alpha);
  start graph by degree-only SAT with E-symmetry), check.sh, run_cfg.sh. Compiled: gcc -O2 -march=native symloc.c -lm.
- run1.sh NAME M K ALPHA SIGA SIGB SECS SEED T0 T1: one run; writes out/NAME/sSEED/ and appends to out/results.tsv.
  NOTE: symloc's internal "best" is its cost (same-side pairs at distance > 6, 0 <=> diameter 7), NOT the scoreboard
  far (all pairs at distance > 7). Scoreboard numbers are always score37's far on the best file (run1.sh prints it).
  Cost 0 implies diameter <= 7 (a cross pair at distance 9 would give a same-side pair at distance >= 8 via a neighbour).
- Temperature: the schedule T0 -> T1 over the iteration budget cools too fast (T 6 -> 0.5 froze at far 168 in 22 s).
  Constant T = 3 works: F21 calibration at n = 168 gave far 0 (diam 7) in < 10 s for seeds 2 and 3 (seed 1 with the
  decaying schedule got stuck at 168). Use T0 = T1 = 3 unless a test says otherwise.

## Calibration runs (constant T=3 unless noted)
- cal168F21 (M=7, K=12, alpha=4, sA=1,1,1,3,3,3, sB=3,3,3,3; the r2f group): seeds 2,3 far 0 (diam 7), < 10 s each.
- n=170 D5 (M=5, K=17, alpha=4, sA=sB=2^8 1): T 40->4: best cost 155 (far 155); T 15->1.5: cost 220 (far 230). Bad.

## 18:21-18:24Z: n=160 calibration, symloc (cost = same-side pairs > 6), T = 3 constant, 25 s, seed 1
(out/results.tsv, out/batch_a.log)
- D5 (M=5, alpha=4, sigma = 2^8 on A and B): best cost/far 195.
- D5 (sigma = 2^7 1^2 on A and B): best 95 (the best n=160 number so far).
- F20 (alpha=2, sigma 4^4 on both): best 220.
- F20 (sigma 4^3 2 1^2 on A; 4^3 2 1 1 on B): disconnected, far 5470.
- Z15 (alpha=1, sigma 3^5 1 on both): disconnected, far 1500. Z15 (3^4 1^4 both): disconnected, far 4800.
  Reading: with alpha = 1 the fixed base vertices give s-fixed fibres; the lift becomes disconnected easily, and
  symloc's cost ignores unreached cross-side pairs, so it does not repair this.
- So none of these reached 0 at n = 160 in 25 s. Calibration target not yet met for Z5 groups.

## 18:23Z: symloc2 (r3a/symloc2.c)
- Same SA and orbit moves, but cost = EXACT score37 far (BFS radius 7 from each orbit representative; far = all
  pairs at distance > 7, weighted by orbit size, divided by 2). symloc's cost only counted same-side pairs, which
  let disconnected graphs look cheap. Check: F21 n=168 with symloc2, seed 2, T=3: far 0 in < 25 s.
- run1.sh uses BIN=./symloc2 when set in the environment; batch.sh runs cfg lines sequentially.

## 18:23-18:26Z: n=170 batch B (symloc2, T = 3, 40 s, seed 1)
- c170_F20a (alpha=2, sigma 4^4 1 on both sides): mkgroup start SAT is UNSAT. Reason: a fixed base vertex a0 needs
  degree 3 from E-orbits under (b,t) -> (sigma b, 2t); with a sigma-fixed b0 and 4-cycles the only orbits are sizes
  1 (b0,0), 2 (2-cycles at t=0) and 4, so 3 = 1 + 2 needs a 2-cycle on the other side. F20a is infeasible.
- c170_F20b (alpha=2, sigma 4^3 2^2 1 on both sides): feasible start, but start graph disconnected; SA best far 240
  (diam 9).
- c170_Z15a (alpha=1, sigma 3^5 1^2): start disconnected (far 9010 at start); SA best far 3060, still disconnected.
- c170_Z15b (alpha=1, sigma 3^4 1^5): far 6000, disconnected.
- Reading: alpha = 1 with 3-cycles keeps the lift disconnected; the orbit SA cannot escape. Fix attempted: run1.sh now
  redraws the SAT start (new SAT seed) until score37 says connected=yes (up to 30 tries).
- Note: the best n=160 D5 config (sigma 2^7 1^2) is the closest to diameter 7 so far (cost 95 at 25 s).

## 18:26-18:40Z: batches C, D (symloc2, exact far; constant T unless noted; 30-40 s; seed 1)
- calibration n=168 with D6 (M=6, alpha=5, sigma 2^7 on both): far 378 (diam 9). Start SAT never connected.
- calibration n=150 with D5 (M=5, alpha=4, sigma 2^7 1 on both): far 90 (T=3), 110 (T=1.5), 85 (T=6). Not 0.
- calibration n=168 with D4 (M=4, alpha=3, sigma 2^10 1): far 320 (diam 8).
- n=180 D5 (sigma 2^9): far 495. D5 (sigma 2^8 1^2): far 390. D6 (M=6, alpha=5, sigma 2^7 1): far 612; D6 (sigma
  2^6 1^3): far 654. Z10 (M=5, alpha=1, sigma 2^9): far 335.
- n=170 D5c (M=5, alpha=4, sigma 2^7 1^3 both): far 280 (diam 8).
- n=160 Z20 (M=5, alpha=1, sigma 4^4 both, group order 20): far 80 (diam 8), the best n = 160 number in this card.
- Temperature: T = 1.5, 3, 6 at n = 150 D5 gave 110, 90, 85. The temperature is not the bottleneck.

### Structural finding (important for n = 170, 180)
- With alpha = 1 (s centralises z) and a sigma FIXED base vertex a0 on A and a fixed b0 on B: the three edges of a0 are
  forced onto b0 (the only size-1 orbits), so the lifts of {a0, b0} form a closed component of 10 vertices.
  The lift is then disconnected and the orbit SA never reconnects it. Observed: Z10 (2^8 1), Z15 (3^5 1^2, 3^4 1^5),
  Z20 (4^4 1) at n = 170 all end disconnected (far 1660-6000).
- With alpha of order 2 or 4 (D5, F20) the orbits of (b,t) under (sigma b, alpha t) have size 2 and connect things;
  D5 and F20 starts reconnect under SA.
- So for n = 170 (odd K = 17) the alpha = 1 groups need sigma WITHOUT fixed base points (cycle types with no 1s, e.g.
  6,6,3,2 or 3^5 2 for order 30). Testing these now.

## 18:38-18:47Z: order-30 and order-20 tests; D5 at n=170 with constant T
- Order 30 (alpha=1, cyclic Z30 = Z5 x Z6 or Z5 x Z3 x Z2 via a single sigma): n=170 starts and SA ends disconnected in
  all three sigma types (6,6,3,2: far 6600; 3^5 2: far 3060; 6,6,2,2,1: far 6400). n=180 with M=6 and sigma 5,5,5
  (Z30 = Z6 x Z5, alpha=1): connected, far 330 (diam 9).
- Z20 at n=170 (sigma 4^4 1, alpha=1): disconnected (far 1660); at n=160 (sigma 4^4, no fixed point) it is connected,
  far 80. Consistent with the closed-component argument above (the closure comes from a fixed base vertex).
- n=170 D5 (alpha=4, sigma 2^8 1 both), symloc2 (exact far), T=3 constant, 80 s: seed 1 far 290, seed 2 far 230.
  The earlier symloc run (same-side cost, T 40 -> 4, 30 s) reached far 155. So the exact-far cost is a WORSE SA target
  here: cross-side pairs at distance 9 add noise that the cost-0 condition does not need (cost 0 already gives diam 7).
- n=170 F20 (alpha=2, sigma 4,4,2,2,2,2,1 both; feasible start, connected after SA): far 200 (diam 9), 60 s.
- n=180 F20 (alpha=2, sigma 4^4 2 both): far 410 (diam 8), 60 s.
- Decision: use the same-side cost (symloc) for SA, and report score37 far of the best file. Batch G tests this at
  n=170 (D5, T=3, 80 s) and at n=150 (D5, T=3, 40 s, same config as cal150_D5a for comparison).

## 18:47-19:00Z: old cost (symloc) vs exact (symloc2), seed sweep, restarts, M = 3 at n = 180
- Batch G (old cost, same-side objective): n=150 D5 T=3 40 s: far 90 (same as symloc2 at T=3). n=170 D5 T=3 80 s
  (seed 1): far 265. n=170 D5 T 25 -> 5 80 s (seed 2): far 175. So the 155 earlier came from the T 40 -> 4 schedule.
- Seed sweep, n=170 D5 (alpha=4, sigma 2^8 1 both), symloc, T 40 -> 4, 30 s, seeds 2..7: far 155, 175, 235, 195, 175,
  220 (score37 far of the best file; symloc cost 155..215). Spread 155-235 over seeds: the schedule works, the seeds
  are scattered, 155 is the best seen (out/t170D5/s2).
- Restarts from the 155 graph (same group, symloc, T 8 -> 2, 60 s, seeds 1 and 2): no change, still 155. The graph is a
  deep local minimum for this move set.
- n=180, M=3 (z of order 3, K = 30), 60 s, T=3 (symloc2):
  alpha=2 with sigma 2^14 1^2 on both sides (group S3, order 6): far 399 (diam 8).
  alpha=1 with sigma 2^15 on both sides (group Z6): far 408 (diam 8).
- Calibration summary at n <= 168 (none reached 0 except the r2f F21 family): D5 at 150: 85-110; Z20 at 160: 80;
  D6 at 168: 378; D4 at 168: 320.

## 19:00-19:12Z: n=170/180 group sweep with same-side cost (symloc, T 40 -> 4, 40 s, seed 2 unless noted)
- n=170 D5 (alpha=4) sigma 2^6 1^5 both: far 155 (a different file from the 155 of 2^8 1, same value).
- n=170 F20 (alpha=2) sigma 4,4,4,2,1,1,1 both: far 4590 (disconnected, cost 2310); sigma 4,2^6,1 both: far 860 (diam 10).
- n=180 D5 (alpha=4) sigma 2^8 1^2 both: far 290. D5 sigma 2^7 1^4 both: far 185 (new n=180 best of this batch).
- n=180 F20 (alpha=2): sigma 4,4,4,2,2,2 both: far 250 (seed 2), 310 (seed 3), 330 (seed 4). sigma 4^4 2 both: far 270.
  sigma 4,4,4,2,2,2 | 4,4,2,2,2,2,2 (mixed): far 950.
- n=180 Z30 = Z6 x Z5 (M=6, alpha=1, sigma 5,5,5 both): far 180 (seed 2, diam 8). Seeds 3 and 4 also end at exactly
  180. So 180 is a floor for this family and this move set, not a lucky seed.
- Tabu variant (r3a/symtabu.c: best of S sampled orbit moves, removed edges tabu for TT steps; env SYMTABU_S, SYMTABU_TT):
  n=180 Z30, 70 s: best 180 (S=40, TT=15); 180 again with S=150, TT=30. The walk drifts to cost 400-600 between
  improvements, so tabu does not beat the SA floor either.
- Far-pair structure (r3a/analyze.py): all these best graphs have their far pairs at distance 8 between SAME-side
  vertices (the F20 file has 10 cross pairs at distance 9). The n = 180 Z30 graph is uniform: EVERY vertex has exactly 2
  far partners (180 far pairs on 180 vertices). The n = 170 D5 graph has far pairs on all 170 vertices. So the floor is a
  per-vertex coverage count, not a few isolated bad pairs.

## 19:12-19:24Z: sigma-type sweep (symloc, T 40 -> 4, 40 s, seed 2): mixed D5 types help
- n=170 D5 (alpha=4), sigma on A and B given as 2^j 1^(17-2j): (j_A, j_B) = (8,7): far 130 (NEW r3a best at 170);
  (7,8): far 130; (7,7): 135; (6,6): 165; (8,8): 210; (5,5): 220. (6,8) and (8,6): start SAT UNSAT (no start).
- n=180 D5 (alpha=4), (j_A, j_B): (7,7): far 185 (same as before); (9,9): 260; (8,8): 290; (9,8), (8,9), (9,7): start
  UNSAT (no start). So for n = 180 the balanced 2^7 1^4 type is best.
- n=180 Z30 variants (alpha=1, cyclic of order 30 or 36): sigma 6,6,6 with M=5: far 180 (same floor); sigma 6,6,3,3 and
  6,6,2,2,2 with M=5: disconnected (far 7200, the start never reconnects); sigma 6,6,3 with M=6: group order 36,
  disconnected; sigma 3^5 with M=6 (Z18): far 288; D6 = Z6 x| Z5-type order-60 (alpha=5, sigma 5,5,5): far 690.
- n=180 with M=3 (K=30), same-side cost, 40 s: S3 (alpha=2, sigma 2^14 1^2): far 267; Z6 (alpha=1, sigma 2^15): far 288.
  (exact-far cost gave 399 and 408 for the same two families.)

## 19:24-19:34Z: seed sweeps of the best sigma types (symloc, T 40 -> 4, 40 s)
- n=170 D5 (alpha=4), (j_A, j_B) = (8,7), seeds 2..5: far 130, 130, 130, 205. (7,8), seeds 2..5: 130, 215, 220, 130.
  (7,7), seeds 2..5: 135, 115, 115, 150. NEW BEST at n=170: far 115 = sigma 2^7 1^3 on both sides, seed 3
  (r3a/best/n170_D5_7_7_far115.edges). Seed spread of about 100 at the same settings: the start matters a lot.
- Restart from the 130 graph (T 10 -> 2, 60 s): no change (130).
- n=180 D5 (alpha=4), sigma 2^7 1^4 both, seeds 2..4: far 185, 195, 235. Best stays 185 (r3a/best/n180_D5_2to7_1to4_far185).
- Next (running at 19:34): restart from the 115 graph; (7,7) at n=170 seeds 5..18; (7,7) at n=180 seeds 5..10.
