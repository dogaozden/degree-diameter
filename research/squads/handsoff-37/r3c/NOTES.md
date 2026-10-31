# r3c NOTES (Haiku worker r3c, squad handsoff-37, card r3c: breakout tabu for lifts at n = 170-180)

Start: 2026-10-31 19:06:15 UTC (date -u). Stop about 21:21 UTC (run until at least 21:06).

Setup: r3c/lift2.c = copy of r2e/lift2.c (breakout tabu engine, built with gcc -O3 -march=native). Groups in r3c/groups
(copied from r2e/groups, S3 generated with mkgroups.sym(3)). Usage: ./lift2 groups/C5.txt 17 SEED SECS OUTPREFIX;
env MODE=bo BOWALK=1 WCAP=16 TEN=8 (r2e's best settings). far = N * raw / 2.
Machine load ~6 on 4 cores at 19:07 (shared), so runs are a bit slower than in r2e.

## 19:06-19:20: engine change = focused moves (lift3.c, MODE=fbo, default)

- lift3.c = lift2.c core (eval, groups, state files) + new main. Modes: fbo (new, default), bo (= lift2 behaviour),
  sa (simulated annealing; tested, worse).
- Focused breakout tabu (fbo): at each step pick one violated (source s, target t) pair uniformly (cnt[s][t] > 0),
  take the base vertices within base distance FR of s and of t, and only consider moves on base edges with an endpoint
  there (volt changes on those edges, and 2-switches between two of those edges). Weights W, bumps at local minima and
  BOWALK as in lift2. The restricted neighbourhood is ~10x smaller, so ~30-40k steps in 45 s instead of ~1k in 90 s.
- Calibration numbers at n = 170, C5 17+17 (45 s runs, far = 5 * raw / 2; the 520 s lift2 runs reached far 110):
  - lift2 bo BOWALK WCAP16 TEN8, 90 s, seed 101: raw 56 (far 140).
  - SA (lift3 MODE=sa), 80 s, T 2 -> 0.2: raw 64 (far 160). T 1 -> 0.15: raw 86. T 0.5 -> 0.1: raw 62 (45 s). SA is
    not competitive: single voltage/2-switch moves change raw by 10-100, so a low-T chain freezes.
  - fbo FR=1 TEN=8 WCAP=16 (seed 102, 45 s): raw 36 -> far 90 (logged, best/n170_C5_fbo_far90.edges).
  - fbo FR=2 TEN=8 WCAP=16 (seed 102): raw 46 (far 115).
  - fbo FR=1 TEN=8 WCAP=16 DECAY=100 (seed 102): raw 46 (far 115). Decay = not better here.
  - fbo FR=1 TEN=8 WCAP=1e6 (seed 103): raw 42 (far 105).
  - fbo FR=1 TEN=4 WCAP=16 (seed 103): raw 26 -> far 65 (logged, best/n170_C5_far65.edges; score37 far 65 diam 8).
- 19:20-19:30 more fbo calibration at n=170 (45-50 s runs, seeds 103-106): TEN4 WCAP16 FR1 gave raw 26, 46, 42, 40 (far
  65, 115, 105, 100); TEN2 raw 46; pure focused tabu (WCAP=1, no weights) raw 40, 42 (so the breakout weights do not
  matter much). Single-run noise is about +-10 raw, so small knob changes cannot be resolved with 1-2 runs each.
  Observation: the global best is reached within ~5-10 s, then 40 s of no improvement (stagnation in one basin).
- Other n with fbo (50 s, seed 201, TEN4 WCAP16 FR1): 176 C4 22+22 far 190 (raw 95); 176 C2xC2 22+22 far 246 (raw 123);
  180 C6 15+15 far 156 (raw 52); 180 S3 15+15 far 264 (raw 88); 180 C5 18+18 far 165 (raw 66); 180 C3 30+30 far 273 (raw 182).
- ELITE POOL (new, lift3.c env POOL=8 PP=60): at each kick, the best state of the excursion since the last kick goes into
  a pool of P distinct states (replace worst); the next kick restarts from a random pool member with prob PP% (else from
  the global best). STALL=1500 with the pool (more kicks: ~20 in 45 s).
  - 170 C5 pool, 45 s, seeds 103 / 104: raw 38 / 30 (far 95 / 75).
  - 180 C6 15+15, POOL 8 PP 60 STALL 1500, 90 s, seed 301: raw 38 -> far 114 (best/n180_C6_far114.edges; score37 far 114
    diam 8; logged, first r3c graph at 180).
  - 180 C5 18+18, same, 90 s, seed 301: raw 56 (far 140).
  - 176 C4 22+22, same, 90 s, seed 301: raw 78 (far 156).
- 19:36-19:50 (all 90 s, pool on, TEN4 WCAP16 FR1 unless noted):
  - 170 C5 seed 301: raw 26 (far 65, same value as the 45 s run; probably the same attractor).
  - 170 C5 FR=2: raw 50 (far 125, only 33k steps: each step is 5x costlier). FR=0: raw 38 (far 95) with 505k steps
    (only the edges at s and t; cheap but too narrow). FR=1 remains best.
  - 170 C5 TEN=6 seed 301: raw 34 (far 85). WCAP=4 seed 302: raw 30 (far 75). Nothing beats raw 26.
  - 180 C6 continuation from the far-114 state (INIT): seed 302 raw 38 unchanged; seed 303 with PERT=25 raw 38 unchanged.
    So the basin is deep and bigger kicks do not leave it.
  - 180 C6 fresh seed 304: raw 42 (far 126).
  - 180 C6 with COMP=100 (sampled compound moves = two focused moves applied together, evaluated as one candidate),
    seed 304: raw 38 (far 114), but 42k steps vs 80k. Unclear gain (the trajectory changes); kept as option COMP.
  - CALIBRATION n = 168, C7 12+12 (the known solution exists), fbo + pool, seed 1, 90 s: raw 8 (far 28). Same as r2e's
    520 s run. The new engine does not find the zero.
- 19:51: background batch batch1.sh started (16 runs x 90 s: 170 C5 x4, 176 C4 x2, 176 C2xC2 x2, 180 C6 x3, C5 x2, C3 x2,
  S3 x1). Results go to out/runs.tsv (labels b1_*), files out/b1_*_s<seed>_best.edges.
- batch1 (90 s each, pool, TEN4 WCAP16 FR1; out/runs.tsv labels b1_*):
  - 170 C5 (k=17) seeds 401-404: raw 38, 34, 34, 40 (far 95, 85, 85, 100). Nothing below the earlier far 65.
  - 176 C4 (k=22) seeds 401-402: raw 91, 75 (far 182, 150).
  - 176 C2xC2 (k=22) seeds 401-402: raw 66, 60 (far 132, 120). Best at 176 so far (C2xC2 beats C4 at this k).
  - 180 C6 (k=15) seeds 401-403: raw 36 (far 108, logged, best/n180_C6_far108.edges), 36 (402, same value), 57 (403, far 171).
  - 180 C5 (k=18) seed 401: raw 70 (far 175).
  Remaining in batch1 at 20:10: 180 C5 seed 402, C3 x2, S3 x1. batch2 (queued, auto-starts after batch1) continues
  the best batch1 state per open case for 90 s (seed 501) and tests COMP=100 and the plain pool at 170 (2 seeds each).
  - 180 C5 (k=18) seed 402: raw 74 (far 185). 180 C3 (k=30) seeds 401, 402: raw 156, 166 (far 234, 249): C3 needs far
    more time (about 80k evals/s, 28 kicks in 90 s).
  - 180 S3 (k=15, S3 = D3 of order 6, generated by mkgroups.sym(3)) seed 401: RAW 12 -> FAR 36 (score37: far 36, diam 8).
    Logged (best/n180_S3_far36.edges, state best/n180_S3_far36.state). This ties the seed near miss (far 36, C3 x S3 5+5
    base) and is the best 180 graph in the squad so far. S3 lifts look like the right family at 180.
- batch3 (queued after batch2): S3 k=14 at n=168 (calibration: does the engine reach 0 on an S3 lift?), S3 k=15 at 180
  (seeds 402, 403), S3 k=16 at n=192 (seed 1; the 192 near miss had far 272-384).
- batch2 (continuations from the best batch1 state per case, seed 501; 170 tests with seeds 501/502), 90 s each:
  - 176 C4 continued: raw 70 (far 140, from 150). 176 C2xC2 continued: raw 60 (far 120, unchanged).
  - 180 C6 continued: raw 36 (far 108, unchanged). 180 C5 continued: raw 68 (far 170). 180 C3 continued: raw 150 (far 225).
  - 180 S3 continued: raw 12 (far 36, unchanged): a plateau.
  - 170 C5 COMP=100: seed 501 raw 48 (far 120), seed 502 raw 26 (far 65, equal to the best). Plain pool: seed 501 raw
    38 (far 95), 502 raw 42 (far 105). So COMP shows no clear gain.
  - Summary of r3c lift bests (all logged): 170 C5 far 65; 176 C2xC2 far 120 (not logged: it is above none of my own
    earlier 176 values but the card says log the first graph at a new n; see scoreboard); 180 S3 far 36; 180 C6 far 108.
- batch3 (20:31-20:37): calibration n=168 S3 k=14 (seed 1, 90 s): raw 28 (far 84), NO zero (the engine does not find an S3
  lift of 168). 180 S3 k=15 seeds 402 / 403: raw 62 (far 186) / 70 (far 210). So the raw-12 result (seed 401) is a lucky
  basin, not typical. 192 S3 k=16 (seed 1): raw 126, far 378 (diam 9; logged as first 192 graph, best/n192_S3_far378.edges).
- CHECK: the 180 S3 far-36 graph (best/n180_S3_far36.edges) has girth 10 and the same sorted per-vertex distance profile
  as the seed shared/seeds/nm180_c3xs3_b5_14.edges (far 36). Very likely the same graph (not an isomorphism test). So the
  S3 15+15 lift search rediscovers the seed near miss from scratch in 90 s, which is a useful calibration of the engine.
- Logged records so far (scoreboard, worker r3c): 170 C5 far 65; 176 C2xC2 far 120; 180 C6 far 108; 180 S3 far 36; 192
  S3 far 378. No far 0 (no diameter-7 graph found at n >= 170).
- batch4 (20:38-20:45, queued): more seeds at 180: S3 seeds 404-407, C6 seeds 404-405.
