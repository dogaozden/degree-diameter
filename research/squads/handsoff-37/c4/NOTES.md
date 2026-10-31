# c4 notes (Haiku worker c4, squad handsoff-37)

Start: 2026-10-31 15:44:32 UTC (date -u). Stop about 17:44 UTC.

Card c4: joint base + voltage search over small groups H with big bases (n = 2kN, k base vertices per side).
Plan: (1) own C engine c4/lift.c with bit-parallel walk-reach cost (sources = 2k base vertices, walks <= 7),
tabu over full voltage-change neighbourhood plus sampled 2-switches; (2) calibrate C7 k=12 (n=168);
(3) run open cases; (4) log best far per n.

## 15:45-15:55 engine and first calibration

- groups/*.txt: multiplication tables (identity 0) from mkgroups.py (C2..C14, C2xC2, C2xC4, C2xC6, C3xC3, C4xC4, C2xC8,
  C2xC2xC4, D3=S3, D4, D5, D6, D7, D8, D9, A4, Q8, F7_3, F5_2). Checked associative with inverses.
- lift.c: base = 3 matchings-worth of edges (eu, ev, ea), E = 3k. Lift vertex (u,g)=u*N+g, blacks (k+v)*N+g. Cost =
  sum over the 2k base sources of lift vertices not reached by walks of length <= 7 (bit-parallel, 64-bit masks; works
  for k <= 32). far = N*cost/2 (checked: score37 agrees, cal_c7k12 cost 20 -> far 70).
  Speed: about 350k-490k evals/s at n = 168.
- Moves: voltage change; 2-switch of the black ends of two base edges (voltages stay on edges). Duplicate lifted edges
  penalised.
- Calibration C7, k = 12 (n = 168, 40 s runs, best cost; lower is better, 0 = solution):
  - SA (T 2 -> 0.3, cycles 10 s): cost 34 and 40.
  - Tabu, 200 sampled 2-switches + all voltage changes, TEN=12: 20 (30 s, seed 1).
  - Tabu, ALL 2-switches (M=-1): TEN=8 gives 14 (seed 5); TEN=20 gives 32.
  - M=-1 TEN=4: 18, 26 (seeds 11, 12). TEN=8 STALL=800: 16, 22. The landscape has large variance over seeds.
- 16:18 n=176 C2xC2 k=22, 520 s, seed 201: cost 50 -> far 100 (score37 agrees). Record at 176 is 86: not an improvement.
  C4 k=22 at 60 s: cost 92 (far 184).
- n=192 survey (60 s each, k=12): C8 cost 74, Q8 78, C2xC4 80, D4 111, C2xC2xC2 148.
- n=192 continuation (INIT = the 520 s best state, 520 s more): no improvement, stuck at cost 68. Plain tabu stalls
  after a few thousand iterations at a fixed level; STALL/PERT perturbation does not escape.
- n=174 C3 k=29, 60 s: cost 124 (far 186; record 97). n=184 C4 k=23, 60 s: cost 133 (far 266).
- n=176 C2xC2 k=22 with RESTART=1 STALL=4000, 500 s (46 restarts): best cost 50 again (far 100). No gain.
- LONG RUN n=182 C7 k=13, 500 s, seed 401: cost 48 -> far 168 (first graph at 182). Logged.
- n=190 C5 k=19, 200 s: cost 122 -> far 305 (first graph). Logged.
- n=186 C3 k=31, 200 s: cost 230 -> far 345, diameter 9 (first graph). Logged.
- n=184 C2xC2 k=23, 150 s: cost 96 -> far 192 (first graph). Logged.
- Scoreboard status: 192 improved 384 -> 272; first graphs at 182, 184, 186, 190.
  No improvement at 170 (record 46), 176 (86), 174 (97) or 180 (36): the tabu engine reached far 110 (n=170, C5 k=17,
  60 s), 100 (n=176, 520 s), 186 (n=174, C3 k=29, 60 s).

## Summary of what the engine does
- Works and is exact (score37 agrees with the cost; C14 k=6 gives a valid n=168 diameter-7 graph in 14 s).
- Good for k <= 12 (n <= 192 with N = 8), weak for k >= 17: the cost of the best tabu state grows quickly with k
  (C5 k=17: 44-56 in 60 s; C3 k=29: 124; C4 k=23: 133).
- Tabu over all voltage changes plus sampled (M=300) or all 2-switches with tenure 8 beats SA (SA at T 2 -> 0.3 gave
  34-40 at C7 k=12; T 1 -> 0.15 stuck at 58). Focused neighbourhoods and random restarts did not help.

## Next steps (if continued)
- Better escape from plateaus at k >= 12: population/elite tabu, or parallel tempering over voltages (the card's idea).
- Use the k = 12 voltage search as a sub-step inside c1/c2 insertion schemes instead of from scratch.
- n=192 Q8 k=12, 500 s, seed 701: cost 74 -> far 296 (not better than C8's 272).
- First graphs (200 s each): n=196 C7 k=14 cost 100 -> far 350; n=200 C5 k=20 cost 176 -> far 440. Logged.

## Logged files (all re-scored with bin/score37 at the end; far matches the scoreboard)
| n | group, k | far | file |
|---|---|---|---|
| 182 | C7, 13 | 168 | c4/best/n182_C7k13_far168.edges |
| 184 | C2xC2, 23 | 192 | c4/best/n184_C2C2k23_far192.edges |
| 186 | C3, 31 (diam 9) | 345 | c4/best/n186_C3k31_far345.edges |
| 190 | C5, 19 | 305 | c4/best/n190_C5k19_far305.edges |
| 192 | C8, 12 | 272 | c4/best/n192_C8k12_far272.edges (state: c4/best/n192_C8k12_far272.state) |
| 196 | C7, 14 | 350 | c4/best/n196_C7k14_far350.edges |
| 200 | C5, 20 | 440 | c4/best/n200_C5k20_far440.edges |

Rebuild of the lifted edge list from a state file: vertex (u,g) = u*N+g for whites u < k, (k+v)*N+g for blacks;
each state line "u v a" is a base edge: (u,g) ~ (k+v, g*a) for every g (N = group order, group table from
`python3 c4/mkgroups.py`). The .edges files are already the lifted graphs, so no rebuild is needed for scoring.
Search code: c4/lift.c (build: gcc -O3 -march=native -o lift3 lift.c -lm; run: MODE=tabu M=300 TEN=8 ./lift3 groups/G.txt k seed secs OUTPREFIX).
- n=192 C8 k=12, second seed 901, 500 s (405k evals/s, 367k iterations): best cost 68 again (far 272). Two seeds at
  the same level suggest a floor for this base size and method, not a bad seed.
- Stop at 17:35 UTC (2 hours). No candidate with far 0 at n >= 170 was found.
