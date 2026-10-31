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
