# r2e NOTES (Haiku worker r2e, squad handsoff-37, card r2e: lift tabu with plateau escape)

Start: 2026-10-31 17:36:04 UTC (date -u). Stop about 19:51 UTC (run until at least 19:36).

Plan: own engine r2e/lift2.c (from c4/lift.c). Modes: tabu (c4 behaviour) and bo (breakout: per (source, target) weights
on the violated pairs, bumped at local minima of the weighted cost). Calibration: C7 k=12 (n=168) cost 0 from the C168.1
quotient (r2e/quot7.py, out/c168_C7k12_state.txt; checked: score37 far 0, diam 7); then random-start calibration; then
perturbation test from the quotient (PERT0 = 5, 10, 20); then n = 170 (C5 17+17), 180 (C6 15+15), 182 (C7 13+13),
192 (C8 12+12).

## 17:37-18:05 engine, calibration, first improvement

- Z7 quotient of C168.1 (quot7.py, from c5/out/aut168.txt: the 504 automorphisms; sig = an order-7 element; 24 free orbits,
  12+12 base, 36 base edges). lift2 INIT check: raw cost 0, score37 far 0 diam 7 (out/c168_C7k12_state.txt).
- lift2.c = c4 engine + breakout weights (MODE=bo: W[s][t] on (source, target base vertex) pairs, +1 on every violated
  pair at a local minimum of the weighted cost; BOWALK=1 also takes the best non-tabu move after a bump; WCAP caps weights).
  Speed about 150-250k evals/s at n=168-182 (846 neighbours per step).
- Calibration C7 k=12 (n=168), random start, raw cost after 60-120 s (seed; lower is better):
  - c4 tabu (MODE=tabu TEN=8, 100 s, seed 1): 18. (c4 notes: 14-20 at 40 s.)
  - bo (no walk, WCAP inf, 120 s, seed 1): 28 (34400 iterations, 32156 bumps: mostly bumps, slow).
  - bo BOWALK=1 WCAP=inf, 100 s, seed 1: 14.
  - bo BOWALK=1, 60 s, seed 2: WCAP 4 -> 20; WCAP 16 TEN 8 -> 20; WCAP 16 TEN 4 -> 38; WCAP 16 TEN 16 -> 28.
  - NOVOLT=1 (2-switches only, voltages fixed): tabu 42, bo 22 (60 s). Voltage moves are needed.
- Basin test from the C168.1 quotient (cost 0): random perturbation then search for 60 s (bo BOWALK WCAP 16):
  PERT0 = 5 -> raw 434 at start, best 20 after 60 s; PERT0 = 10 -> start raw 492, best 22; PERT0 = 20 -> start 672, best 18.
  So the search does not return to the known solution; it goes to the same 14-22 level as from random starts.
- One-move neighbourhood of the C168.1 quotient (nbhist.py): ALL 216 voltage changes give raw cost >= 102 (the landscape
  is very rugged for voltage moves); 2-switches give 12 neighbours with raw cost 0 (other diameter-7 lifts at distance 1)
  and then 50, 66, 84, ... The 2-switch moves are the useful ones.
- n = 182, C7 k = 13 (240 s each, seed 11): bo BOWALK WCAP 16 TEN 8: raw 40 -> far 140 (score37: far 140, diam 8).
  Plain tabu: raw 46 -> far 161. c4 had far 168 after 500 s. LOGGED to the scoreboard (improvement at 182:
  r2e/best/n182_C7k13_far140.edges, state r2e/best/n182_C7k13_far140.state).

- n = 168 calibration, breakout-walk (WCAP 16, TEN 8), 520 s, seed 21 (random start): best raw 8 (far 28; out/cal168_bo_s21_best.edges).
  No cost-0 lift found; the best raw in the last 400 s stayed at 8. (Raw 14 at 100 s on other seeds.) Improvement over tabu (18-20 at 60-100 s).
- n = 192, C8 k = 12, bo (520 s, seed 31): raw 74, far 296 (score37 agrees). WORSE than c4's far 272 (raw 68) and not logged.
  Breakout bumps are 75% of iterations here (a sign the weights grow fast for k = 12 and N = 8).
- n = 182 continued from the far-140 state, bo 520 s (seed 41): raw 36 -> far 126 (score37 far 126 diam 8). LOGGED
  (r2e/best/n182_C7k13_far126.edges, state .state).
- n = 182 continuation 2 (from far 126, bo WCAP 16, 520 s, seed 51): no change (raw 36). Continuation 3 (PERT 16, STALL 1500,
  WCAP 8, 520 s, seed 61): no change (raw 36, 65 kicks). The raw-36 basin is deep; kicks from its best do not leave it.
- n = 170, C5 k = 17, bo (520 s, seed 71): raw 44, far 110 (score37 far 110). Same as c4's 60 s tabu (far 110); no gain. Not logged.
- n = 184, C2xC2 k = 23: bo (all 2-switches, 520 s, seed 81): raw 184, far 368 (bumps 26754 of 27312 steps: weights dominate).
  BUMPGAP=10 (300 s): raw 202. Plain tabu with ALL 2-switches (150 s): raw 251, far 502. The neighbourhood is too big at
  k = 23 (2760 evaluations per step, 7k steps in 150 s). c4 used M = 300 sampled 2-switches and got raw 96 in 150 s, so
  large k needs the sampled neighbourhood (M = 300), not the full one. Lesson recorded; rerun with M = 300.
- n = 184, C2xC2 k = 23, bo with M = 300 sampled 2-switches (300 s, seed 91): raw 100, far 200 (c4 has 192). Not logged.
- n = 190, C5 k = 19, bo with M = 300 (520 s, seed 101): raw 114, far 285 (score37 far 285, diam 8). LOGGED (beats c4's 305):
  r2e/best/n190_C5k19_far285.edges and .state.
- n = 190 continuation from far 285 (bo M = 300, 480 s, seed 111): raw 88, far 220 (score37 far 220 diam 8). LOGGED
  (r2e/best/n190_C5k19_far220.edges, .state). Current best of this worker at 190.

## Summary (stop 19:36 UTC)
- Best far per n (all lifts, score37-checked, all logged): n=182 far 126 (C7 k=13), n=190 far 220 (C5 k=19). No far 0 at n >= 170.
- Calibration n=168 (C7 k=12, the card's key test): breakout-walk reaches raw 8 in 520 s (far 28), tabu 14-20 at 60-100 s.
  Still no cost-0 lift from a random start, and the known C168.1 quotient is isolated in the voltage landscape (every voltage
  change there costs >= 102 raw; only 12 of 630 2-switches keep cost 0).
- Plateau escape that helped: breakout weights with a tabu walk (BOWALK=1, WCAP 16). Helps at k = 13 and 19 (n = 182, 190),
  not at k = 12 with N = 8 (n = 192: far 296 vs c4's 272), and not at k = 23 (n = 184: far 200-368 vs c4's 192). Weight bumps
  dominate the steps for k >= 17 (BUMPGAP did not fix it at k = 23). Path relinking / elite pool not tried (no time).
- Most promising next step: plateau escape on the sampled neighbourhood for k = 12 (M = 300 instead of all 2-switches), and
  a 2-switch-only pass after each voltage pass (voltage moves are catastrophic in the rugged landscape), with 520 s runs
  from the n = 182 far-126 state (r2e/best/n182_C7k13_far126.state).

## How to rebuild / rerun
- Build: gcc -O3 -march=native -o lift2 lift2.c -lm (r2e/). Run: MODE=bo BOWALK=1 WCAP=16 TEN=8 [M=300] [INIT=state] ./lift2 groups/GROUP.txt k seed secs OUTPREFIX.
- Files: r2e/best/n182_C7k13_far126.edges (score37 far 126), r2e/best/n190_C5k19_far220.edges (far 220); the .state files are
  "N k" then "u v a" per base edge (same format as c4, usable with INIT=).
- Z7 quotient of C168.1: python3 r2e/quot7.py r2e/out/c168_C7k12_state.txt (checks the lift reproduces conder168).
