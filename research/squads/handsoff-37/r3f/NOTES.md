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
- 20:13-20:24 results (lift3 defaults POOL 8 PP 60 STALL 1500 FR 1 TEN 4 WCAP 16, 20 s per run, seeds 2000..2009, k = 12):
  - D4: far 416..496 (raw 104..124). Q8: far 272..392 (best raw 68 = far 272). C8: far 272..352 (raw 68 twice = far 272).
    None beats 256. Order-8 groups ranked: C2xC4 256 < Q8 = C8 272 < D4 416 < C2xC2xC2 592.
  - Subgroup lifts of the far-256 graph (40 s each, from the INIT state): H = C4b (<3>), 128 = far 256 unchanged;
    H = C2xC2 (<2,4>), 128 = far 256 unchanged. Also the C4 (<1>) run above. No improvement.
- 20:24 knob variants on C2xC4 k=12 queued (batch3.sh, 8 seeds x 20 s each): STALL 600 POOL 4 PP 40 TEN 6 (out/batch3_stall600.tsv),
  TEN 8 (batch3_ten8.tsv), POOL 0 (batch3_pool0.tsv).
- 20:30 C2 subgroups (base 48+48, k = 48) NOT run: lift3 (MAXK 32) rejects k = 48; the copy built with MAXK 64 (lift3_64) reports
  start raw 0 for N = 2 although score37 of the same state is far 256. So lift3's cost is wrong for N = 2 with this base
  (cause not found; N = 4 and 8 match far = N*raw/2 exactly). Do not use lift3 for C2 lifts until fixed. Queued sub2 runs cancelled.
- 20:26-20:29 knob variants on C2xC4 k=12 (8 seeds each, 20 s): STALL 600 POOL 4 PP 40 TEN 6: far 256..408 (best 256 twice);
  TEN 8: far 396..424 (best 256 once). No variant beats the 256 attractor.
- 20:33 cause of the lift3 N = 2 failure: eval() keeps the walk sets of base vertices in ONE uint64 per lifted vertex
  (`full = (1ULL << (2*k)) - 1`), so it needs 2k <= 64, i.e. k <= 32. For k = 48 the high bits are lost and raw is 0 falsely
  (lift3_64 with MAXK 64 is therefore invalid for k = 48). Fix would be a 2-word bitset (R, R2, cnt, full). Not done (time).
  Any C2 subgroup lift of the far-256 graph (base 48+48 over C2) is still untested.
- 20:33-20:35 C2 SUBGROUPS (after fixing the bitset limit: lift3w.c = lift3 with two-word bitsets and MAXK 64; start raw 256 =
  far 256 for N = 2, matches score37; the C2xC4 start is still raw 64):
  - C2a = <2> (base/c2c4_C2a_k48.state, 40 s, seed 821): best raw 256 (= start), far 256. No improvement.
  - C2b = <4> (40 s, seed 821): best raw 256, far 256. No improvement.
  - C2c = <6> (85 s, seed 823, POOL 8): best raw 256, far 256. No improvement.
  So the far-256 graph is also a strict local minimum for breakout moves inside the C2, C4 and C2xC2 families.
- 20:35 background batch3 "last" (16 seeds, default knobs, C2xC4 k=12, out/batch3_last.tsv) started.

## How to rebuild the logged n = 192 graph (far 256)

- Logged file: r3f/best/n192_C2xC4k12_far256.edges (score37: n=192 far=256 diam=9; apsp: not a diameter-7 candidate).
  State: r3f/best/n192_C2xC4k12_far256.state (lift3 format "N k" then "u v a"; N = 8, k = 12, group groups/C2xC4.txt).
- Rebuild from scratch: gcc -O3 -march=native -o lift3 lift3.c -lm; then
  POOL=8 PP=60 STALL=1500 FR=1 TEN=4 WCAP=16 ./lift3 groups/C2xC4.txt 12 401 22 out/x   (the seed-401 run; other seeds give 256
  too, e.g. 404, 1002, 1006, 1007, 1012: all one attractor by WL hash). Output: out/x_best.edges (far = 8*raw/2 = 256).
- Groups: groups/C2xC4.txt (table, identity 0; element indices as in the file). C2xC4 k12 is the best order-8 group at 192
  (C2xC4 256 < Q8 272 = C8 272 < D4 416 < C2xC2xC2 592; order 4 and 6 worse: C4 k24 382, C2xC2 k24 304, C6 k16 330, S3 k16 429).

## Summary (stop 21:15Z)

- Records: n = 192: far 256 (was 272). No far 0 anywhere (no candidate).
- Breakout weights on the unsymmetric near misses (n = 180 far 36, n = 192 far 256/272): no improvement in any run. All 2-switch
  neighbours of these graphs are uphill by >= 41 (n = 180) or >= 43 (n = 192); the breakout walk climbs to raw 130-850.
- Keeping a subgroup of the near miss / the far-256 graph: C3 (free, 30+30) of the 180 near miss: no move below 24 (far 36).
  C4 (two choices) and C2xC2 (k = 24) and C2 (three choices, k = 48, two-word lift3w): all stay at far 256 (start).
- lift3 limit found: the original lift3 is limited to 2k <= 64 (single-word bitsets); lift3w.c (two words) fixes it.
- 20:40 final batch (16 seeds 3300..3315, default knobs, C2xC4 k12, 20 s each): far 256 in 5 runs (raw 64), 304..444 otherwise.
  Nothing below 256. Total C2xC4 k12 runs this worker: about 60 (all <= 256 at best, 256 is the floor found).
- Stop 20:41: no background run of mine is left.
- 20:42 C2 lift of the 180 near miss (free involution, base 45+45, mk_c2base.py, base/nm180_C2_k45.state; start raw 36 = far 36,
  checked by score37), lift3w breakout 40 s x 2 seeds (831, 832, POOL 8): best stays 36. No improvement.
- Final state at 20:42: best far at n = 192 is 256 (r3f/best/n192_C2xC4k12_far256.edges). Nothing at n = 180 below 36.
