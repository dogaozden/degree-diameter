# r3g NOTES: Z5-symmetric orbit insertion, m = 80 (n = 160) -> m = 85 (n = 170)

Start: 2026-10-31T19:45Z (date -u). Stop by 21:15Z, final notes then.

## Plan
- Engine: r2c/lift2.c (copied). Polarity double cover of M = Z5-symmetric 3-regular graph with loops, k base
  vertices (m = 5k), cost = unordered pairs {i,j} of M with no even walk <= 6; far of the cover from bin/score37.
- Step 1: many zero-cost bases at m = 80 (k = 16) with lift2 (different seeds).
- Step 2 (grow.c, includes lift2.c): add ONE base vertex w (index 16 = one Z5-orbit = 5 M-vertices, 10 cover vertices).
  Exhaustive insertions:
  A: subdivide a base edge (a,b,g) into (a,w,g1), (w,b,g2) plus a 1-stub M-loop at w (g = 0): 23 x 25 choices.
  B: remove two base edges e1, e2; w joined to one endpoint of each (voltages h1, h2), the other two endpoints joined
     (voltage h3), plus 1-stub loop at w: 253 pairs x 4 x 125 voltages.
  Every insertion keeps the Z5 symmetry (it is a base-level change); score the cost of each (exact, cheap).
- Step 3: SA repair with lift2's stub-preserving moves from the best few insertions (Z5 only).

## 19:45-19:55Z results so far
- Zero-cost m=80 (n=160) Z5 base from lift2, seed 31: `out/z80s31_best.items` (cost 0, 25 s run). Seeds 32, 33: cost 5
  after 25 s (not zero). Seeds 34-41 run with 75 s each (out/z80s3x.log): 34 -> 20, 35 -> 25, 36 -> 5 (zero is not
  reliable at this budget).
- grow.c (includes lift2.c): base vertex insertion. A = subdivide an edge with w (575 choices), B = two edges removed,
  w joined to one end of each + other ends joined + 1-stub loop at w (121k), C = three edges removed, w joined to one end
  of each, one leftover end gets a 1-stub loop, two leftover ends joined (5.1M, h1 = 0 WLOG). Enumeration ~25 s.
- Seed 31 base: insertion floor = 45 (B and C tie; A >= 75). score37 of the cost-45 cover: far 90 at n = 170
  (out/g31_best.edges). SA (lift2 moves, T 1.5 -> 0.2 and hot 3 -> 0.3, 20-30 s from the top 3 candidates): no move
  below 45. Exact re-solve (r2c/lns) of this candidate: 3-subsets (680, 7.8k completions) and 4-subsets (2380, 472k):
  best 45. 5-subsets: 32M completions in 100 s (killed), best 45.
- So the one insertion so far is locally optimal at 45 (far 90), worse than the direct Z5 floor 40 (far 80).

## 19:57-20:00Z: more parents
- Batch (lift2, 2M iters/restart, 30 s, seeds 51-60): zero cost at seeds 53 and 55; cost 5-25 otherwise
  (seed 51: 15, 52: 25, 54: 25, 56: 5, 57: 10). Seeds 31 and 40 are zero too (75 s batch). So zero m=80 bases are
  found in about 1 of 3 runs of 30-75 s; cost 5 is a frequent trap (one uncovered orbit of pairs).
- Option D added (w gets a 2-stub loop and one edge; a 1-stub loop elsewhere is replaced by an edge): min 110-160,
  never useful.
- Insertion floor (min over options A, B, C; C evaluated only for zero parents) per parent, cost at m = 85:
  zero parents: seed 31/40 -> 45 (B and C), seed 53/55 -> 65 (B, C); cost-5 parents: seed 33 -> 50 (A and B),
  seeds 32/36/37/38/39/56 -> 50 (B); cost-15/25 parents: 80-145. No parent gives an insertion floor below 45.
- pipe.sh (insertion + 3 SA repairs of 12 s each) on seed 53: floor 65, SA stays at 65 (far 130).
- Verdict so far: a Z5 orbit insertion into a zero m = 80 cover gives cost 45 (far 90) at n = 170; SA does not
  move from it and the exact 4-subset re-solve does not move from it either. Direct Z5 floor at m = 85 is 40 (far 80,
  r2c). The insertion route is worse by one orbit (5 pairs).
- Why m = 82 and m = 84 cannot be Z5 seeds (card's "m = 82 -> 85, m = 84"): a Z5 acting on M (a symmetric 0/1 matrix
  with row sums 3) has orbits of size 5 or 1. A fixed M-vertex has 3 neighbours, which must form a union of orbits, so
  they are all fixed; the fixed set is then a closed cubic component of M, and M is connected for diameter 7. So m must be
  0 mod 5 (80, 85, 90). Only m = 80 and 85 are in play here.

## 20:00-20:05Z: breakout (clause weighting) repair, grow.c BREAK=K mode
- breakout_run(): weights W[i][j] on uncovered same-side pairs (cover6 bitset N^6), accept if weighted cost does not
  increase, bump weights of the uncovered pairs after K non-improving proposals; real cost tracked separately.
- Calibration (m = 80, n = 160, 30 s): seed-34 parent cost 20 -> 10 (plain lift2 SA: 20 after 75 s). So the breakout
  escapes better than SA, but still no zero. Seed-32 parent cost 5: stays 5.
- On the m = 85 insertion candidate (cost 45, seed 31): breakout K = 100 (40 s, 11M proposals, 25k bumps): 45;
  K = 20 (45 s): 45.
- On the r2c cost-40 Z5 floor at m = 85 (r2c/out/t85a_best.items, 60 s, 18.9M proposals, 17k bumps): 40. No escape.
- Exact 5-subset re-solve (all 6188 subsets of the 17 base vertices, 45.8M completions, 20:07Z) of the seed-31
  insertion candidate: best 45. So this candidate is 5-subset locally optimal (like the r2c floor).

## 20:08-20:16Z: more zero parents, two-stage insertion
- Batch of lift2 runs (seeds 100-125, 30 s each, out/batch_parents.log): zero parents are rare; seeds 100-112 gave
  costs 5-35 only (no zero). Zero m=80 parents so far: seeds 31, 40, 53, 55 (all found in 25-75 s runs).
- m = 75 (n = 150) parents with lift2 25 s: seed 1 cost 10, seed 2 cost 5. Zero at m = 75 not reached either.
- grow2s.c (two-stage insertion, includes repair.h): stage 1 inserts one orbit into the parent (4.5M evaluations),
  keeps the 20 best covers, stage 2 inserts a second orbit into each (2.4M evaluations). Test on the m = 75 cost-5 parent
  (out/p75s2_best.items): stage-1 best 35, stage-2 best 75 (D), SA from 75 stays at 75. Two greedy orbit insertions are
  worse than one insertion from a zero parent (45).

## 20:17-20:22Z: breakout calibration at m = 85 (random starts) and m = 80
- Random Z5 start at m = 85 (k = 17), breakout K = 100, 60 s: seed 7 -> cost 40, seed 8 -> cost 45.
- K = 300 (too few weight bumps, 24 in 90 s): cost 60. K = 30, 90 s, seed 22: cost 40 (381k bumps), saved as
  r3g/best170_z5_breakout_far80.edges (score37 far 80, diam 8; apsp INVALID as expected, not a record).
  So from random starts the breakout repair finds the same cost-40 floor (far 80) as the plain SA of r2c.
- Random Z5 start at m = 80 (k = 16), breakout K = 100, 60 s: cost 5 (not zero). The m = 80 zero covers are rare for
  every method here; the m = 85 floor (40) is reached more easily than m = 80 zero.
- Breakout random m = 85 runs (95-90 s each, K = 30 or 50): seeds 22, 23, 24, 25 -> cost 40 each (seed 21, K = 300:
  60). Distance-profile invariant (inv.py: per-vertex distance histograms, hashed): the cost-40 covers form several
  classes: seeds 7 and 25 share one, 23 and 24 another, 22 (= best170_z5_breakout_far80) and 8 and the r2c floor are
  each different. So the cost-40 floor is reached by several inequivalent Z5 bases, all far 80.
- 20:31-20:36Z: seed 31 breakout K = 30: 45; seed 32 K = 30: 40; seed 33 with K = 40 (95 s): COST 35, far 70
  (score37 verified: n 170, far 70, diam 8; saved r3g/best170_z5_breakout_far70.edges, items alongside). The first
  Z5 polarity cover below the cost-40 floor in this job. Still above the board (46). Logged to scoreboard (far 70).
- Insertion candidate (seed 31) with breakout K = 30, 85 s: 45 (no change).
