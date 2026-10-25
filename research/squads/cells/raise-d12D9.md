# Raise the (Δ,D) = (12,9) record (Haar graphs)

Job "raise-12-9", Haiku worker, branch `claude/raise-d12d9-bipartite-record-f510kc`.
Record to beat: **34,026,720** vertices = 2N, N = |SL(2,41) × Z_247| = 17,013,360, k = 3, m = 4, f = 0
(`research/frontier/sols/d12D9_sl_41_247_orb3f0_s1.txt`, μ = 16.3, solved in 3.8·10⁴ evaluations).
Table value 30,001,152 (survey, Table 4). Moore bound 471,589,538.

Every new record must have N > 17,013,360 and pass an independent checker:
- SL(2,p) × Z_n above 20M vertices: `research/frontier/haarcheck_sl.c` and `research/structured/tools/haarcheck2.c`/`hc2`
- PSL(2,p) × Z_n above 20M vertices: `research/structured/tools/haarcheck_psl.c`
- below 20M vertices: `research/frontier/build_haar2.py`

## Method
`ORBIT="3 4 0" THREADS=1 haar_sym 12 9 SECS SEED 8 OUT GROUP... n` (f = 0: 4 free α-orbits of size 3, no identity).
Screen: `tools/orb_screen.py 12 9 LO HI "3 4 0" --samples 600 --bin ...` (random symmetric S, ranks by lower cost tail).

## Log
(see below; newest last)

### Round 1 (started 07:41 UTC, 40 min each, THREADS=1, k=3 m=4 f=0, K=8)
Groups above the record (N > 17,013,360), μ from haar_sym's own header:
- psl 53 × Z229, N = 17,040,348, μ 16.67, |Fix| 26 — cost 3 after 90 s
- psl 61 × Z151, N = 17,132,460, μ 18.06, |Fix| 29 — cost 6 after 90 s
- psl 47 × Z331, N = 17,174,928, μ 18.73, |Fix| 23 — cost 15 after 2 min
- sl 37 × Z337, N = 17,057,592, μ 16.92, |Fix| 35 — cost 24 after 90 s
Logs: research/structured/runs/d12D9_<group>_s1.log (copied from the scratchpad runner).
Screening note: orb_screen's random-sample ranking costs ~0.5 s per sample (too slow for a 60-group window);
annealing runs at ~10 evaluations/s per process at N ≈ 1.7·10⁷ with four processes in parallel. Dropped the screen.

### Round 1 result: NEW RECORD 34,264,920 (+0.7 % over 34,026,720)
- psl 61 × Z151, N = 17,132,460, k = 3, m = 4, f = 0, seed 1, μ 18.06, |Fix| 29: **solved** at 6,377 evaluations (877 s).
  File: research/frontier/sols/d12D9_psl_61_151_orb3f0_s1.txt. Log: research/structured/runs/d12D9_psl_61_151_orb3f0_s1.log.
  Check: haarcheck_psl (low-memory PSL checker): VALID d=12 D=9, both sides reach all 17,132,460 per side, ecc 9.
  Not yet re-checked by build_haar2.py (too large: ~2·10⁷ vertices, hours and > 7 GB).
- Others at 40 min budget: psl 53 × 229 best 3, psl 47 × 331 best 3, sl 37 × 337 best 14 (still running at this point).

### Round 2 (from 08:00 UTC): bar is now N > 17,132,460
Stopped sl 37 × 337 (N 17.06M) and psl 53 × 229 (N 17.04M): below the new record, a solution there would not count.
Running: psl 47 × Z331 (N 17,174,928, μ 18.7), sl 43 × Z217 (N 17,243,688, μ 19.9), psl 89 × Z49 (N 17,269,560, μ 20.3),
sl 97 × Z19 (N 17,338,944, μ 21.5). Each 40 min, seed 1, k=3 m=4 f=0.
Runner: scratchpad run.sh (haar_sym with THREADS=1, nice, timeout; copies logs to research/structured/runs/d12D9_<tag>.log).
