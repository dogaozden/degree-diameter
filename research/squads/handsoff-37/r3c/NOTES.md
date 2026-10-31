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
