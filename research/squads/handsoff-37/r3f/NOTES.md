# r3f NOTES (Haiku worker r3f, squad handsoff-37, card r3f: breakout weights at the n = 180 and 192 near misses)

Start: 2026-10-31T19:45:34Z (date -u). Stop by 21:15Z (final notes then).


## 19:45-20:00 unsymmetric breakout (bo2.c): NEGATIVE, numbers

- bo2.c: focused breakout tabu over 2-switches on the UNSYMMETRIC graph (cost = weighted same-side pairs at distance > 6;
  raw = unweighted count, raw 0 iff diam 7; far (score37) >= raw). Build: gcc -O3 -march=native -o bo2 bo2.c.
  Usage: FR=1 TEN=8 WCAP=16 BOWALK=1 ./bo2 EDGES SECS SEED OUTPREFIX (env DELTA = raw band, RESTORE, SAMPLE, STALL, DIAG=1).
- Landscape (DIAG=1, full 2-switch neighbourhood):
  - nm180 far 36 (raw 36): ALL valid 2-switches give raw >= 77 (mean 160). Strict local minimum, every move uphill >= 41.
  - n192 C8k12 far 272: ALL valid 2-switches give raw >= 293 (mean 406). Also a strict local minimum.
- Results (no improvement in any run):
  - n180 near miss, BOWALK=1 WCAP 16 FR 1, 30 s: best 36, but the walk drifts to raw 550-600 within 10 s.
  - WCAP 2 and 4 with BOWALK=1: same drift (current raw 600). BOWALK=0 WCAP 16: weights saturate at the cap (wcost 576 =
    36 x 16), no move ever accepted (16k bumps).
  - FR=2 BOWALK=0: current raw drifts to 319-429. FR=1 WCAP=1 (plain focused tabu) on n192: raw climbs 272 -> 850 in 30 s.
  - DELTA (raw band: accept moves only with raw <= best + DELTA): DELTA 20 = no admissible move at all (min neighbour is
    +41); DELTA 60 and 100: best 36 unchanged (raw wanders to 131); n192 DELTA 60: best 272 unchanged, current raw 330.
  - Calibration from a RANDOM cubic bipartite start, n = 140 (gen_rand.py 70 1), 45 s: best raw 53. c7's plain SA/PT got
    far 5 at n = 140, so this focused breakout is WEAKER than simple annealing on unstructured graphs. Not useful here.
  - Conclusion: on the unsymmetric near misses, breakout weights make the walk climb (the new violated pairs are cheap, the
    old ones pile up at the cap). The near misses are isolated minima; breakout does not reach a lower basin in 30-60 s.

## 20:00-20:10 n = 192 lifts (the gain of this job so far), and a C3 subgroup test at 180

- lift3 (copied from r3c; breakout focused tabu, POOL 8 PP 60 STALL 1500 FR 1 TEN 4 WCAP 16; 20-22 s per run, seeds 401..)
  over the four order-8 groups at n = 192 (k = 12): C2xC4 raw 64 -> far 256 (seed 401, 22 s) <- NEW BEST at 192 (old 272).
  D4 far 416, Q8 far 328 (raw 82), C2xC2xC2 far 592; (all 22 s, seed 401). Order 4 and 6 at k = 24 / 16 (20 s): C4 far 382,
  C2xC2 far 304, S3 far 429, C6 far 330.
  - C2xC4 other seeds (21 s): 403 raw 100, 404 raw 64 (far 256 again), 405 raw 104, 406 raw 80. 85 s run (seed 402): raw 72
    (far 288). Parameter variants (20 s, seed 601): TEN 8 raw 104, WCAP 4 raw 110, FR 2 raw 120, no pool raw 72.
    Continuations from the far-256 state (INIT, seeds 501-503, 25 s): raw stays 64 (the basin is deep).
  - So the search is high-variance: short restarts find 256 or 300-400. A batch of 40 seeds x 20 s on C2xC4 is running
    (out/batch_C2xC4_k12.tsv; its stdout was lost by a bug in batch192.sh, so score the out/b_C2xC4_k12_s*_best.edges files).
- Lift of the 180 near miss over a FREE C3 (mk_c3base.py: free order-3 automorphism from c2/out/auts_c3s3.json, base 30+30,
  base file base/nm180_C3_k30.state; start raw 24 = far 36, checked with lift3 INIT): breakout lift 40 s (seed 701, INIT,
  POOL 8): best stays 24 (far 36); the current raw drifts to 250 as in the unsymmetric runs. No improvement.
- 20:08 batch of 40 seeds (C2xC4 k12, 20 s each, out/b_C2xC4_k12_s1000..1039_best.edges; scored with score37 after each run):
  first six: far 408, 400, 256 (seed 1002), 288, 344, 424. The 256 floor (raw 64) recurs. Queued after it (batch2.sh, 10 seeds
  each, out/batch2_<G>_k12.tsv): D4, Q8, C8 at k = 12 (C8 is c4's group: is 272 beatable with restarts?).
- 20:10: the far-256 hits (batch seeds 1002, 1006, 1007, 1012 and the logged best) have the same Weisfeiler-Lehman hash
  (networkx, 5 rounds): one attractor graph. Seed 2001 with POOL 16 PP 40 STALL 1000 (85 s): far 288. The batch so far:
  256 x4, 288 x2, 328, 344, 360, 400, 408, 416, 424 (13 runs).
- 20:12 SUBGROUP lift of the far-256 graph (keeping a free subgroup of C2xC4, the card's "keep a subgroup" idea):
  mk_sub.py / mk_sub2.py derive the state over H (base vertices (u,c) for cosets c of H, voltage = H-exponent). Checked with
  lift3 INIT: start raw 128 = far 256 (score37 confirms) for H = C4 (<x> with x of order 4), H = C4b (<3>) and H = C2xC2 (<2,4>).
  - H = C4 (base/c2c4_as_C4_k24.state, k = 24, 85 s, seed 801, POOL 8): best raw stays 128 (far 256); current raw drifts
    (the same walk behaviour as before). No improvement.
  - H = C4b and H = C2xC2: queued (sub_runs.sh, 40 s each); see out/sub_runs.tsv.
- 20:13 an accident: two D4 batches ran at once (a stale chain from my first queue plus the new one; same output names).
  Killed the duplicate (PIDs 23656, 23734, 23736). The surviving D4 batch's seed 2000 output may be overwritten: its tsv row
  is from the surviving run only.
