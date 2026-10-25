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

### Round 2 result: NEW RECORD 34,677,888 (+1.2 % over 34,264,920, +15.6 % over 30,001,152 table)
- sl 97 × Z19, N = 17,338,944, k = 3, m = 4, f = 0, seed 1, μ 21.5, |Fix| 95: **solved** at 11,817 evaluations (1,015 s).
  File: research/frontier/sols/d12D9_sl_97_19_orb3f0_s1.txt. Log: research/structured/runs/d12D9_sl_97_19_orb3f0_s1.log.
  Checks: haarcheck_sl (frontier/haarcheck_sl.c) VALID and haarcheck2 (frontier/haarcheck2.c) VALID, both d=12 D=9, all 17,338,944 per side reached, ecc 9.
- Still running at this point: psl 47 × 331 (cost 3), sl 43 × 217 (cost 14), psl 89 × 49 (cost 5).

Round-2 remaining runs finished unsolved (below the bar after the record, so not useful): psl 47 × 331 best 3 (2210 s),
sl 43 × 217 best 14, psl 89 × 49 best 5.

### Round 3 (from 08:19 UTC): bar is N > 17,338,944 (34,677,888)
Running: psl 59 × Z169 (N 17,349,540, μ 21.7), psl 71 × Z97 (N 17,355,240, μ 21.8), pgl 37 × Z343 (N 17,361,288, μ 21.9),
psl 83 × Z61 (N 17,436,972, μ 23.4). Each 40 min, seed 1, k=3 m=4 f=0.
Note for resumers: the in-container clock and the tool "sleep" timings are unreliable; use foreground until-loops with
an explicit timeout to wait for runs.

Round 3 finished unsolved after 40 min: psl 59 × 169 best 6 (28.7k evals), psl 71 × 97 best 3 (23.7k), pgl 37 × 343 best 6 (48.6k),
psl 83 × 61 best 6 (22.4k). All above the bar, all unsolved.

### Round 4 (from 08:59 UTC): same bar, N > 17,338,944
Running: psl 71 × 97 seeds 2 and 3 (N 17,355,240, μ 21.8, best cost 3 in round 3), psl 139 × Z13 (N 17,455,620, μ 23.7),
psl 47 × Z337 (N 17,486,256, μ 24.3; no wide rows, so slower per evaluation).

### Round 4 result: NEW RECORD 34,710,480 (+0.1 % over 34,677,888)
- psl 71 × Z97, N = 17,355,240, k = 3, m = 4, f = 0, seed 3, μ 21.8, |Fix| 35: **solved** at 13,745 evaluations (1,255 s).
  File: research/frontier/sols/d12D9_psl_71_97_orb3f0_s3.txt. Log: research/structured/runs/d12D9_psl_71_97_orb3f0_s3.log.
  Check: haarcheck_psl VALID d=12 D=9, all 17,355,240 per side reached, ecc 9. (Only PSL low-memory checker applies; no second PSL checker here.)
- Still running at this point: psl 71 × 97 seed 2 (best 3), psl 139 × 13 (best 18), psl 47 × 337 (best 12, slow evaluation).

### Round 5 (from 09:44 UTC): bar N > 17,355,240 (34,710,480)
Unsolved, above the bar: psl 139 × 13 best 17 (22.5k evals), psl 47 × 337 best 6 (10.5k evals, haar_gen3 evaluator, no wide rows).
Stopped unpromising: psl 43 × 439 (best 18 at 20 min, haar_gen3 evaluator); psl 71 × 97 seed 2 (N equal to the record, could only tie).
Running: pgl 37 × 343 seed 2 (best 8 so far), psl 47 × 337 seed 2, sl 71 × 49 seed 1 (N 17,534,160, μ 25.3).

### Round 5 result: NEW RECORD 35,068,320 (+1.0 % over 34,710,480)
- sl 71 × Z49, N = 17,534,160, k = 3, m = 4, f = 0, seed 2, μ 25.3, |Fix| 71: **solved** at 23,473 evaluations (1,674 s).
  File: research/frontier/sols/d12D9_sl_71_49_orb3f0_s2.txt. Log: research/structured/runs/d12D9_sl_71_49_orb3f0_s2.log.
  Checks: haarcheck_sl VALID and haarcheck2 VALID, both d=12 D=9, all 17,534,160 per side reached, ecc 9.
- The same group, seed 1 (40 min, 34.6k evals) ended at best 2. Seed matters: this is a ~1-in-2 group at μ 25.
- Unsolved above the old bar: pgl 71 × 49 best 9, sl 47 × 169 best 6.

### Round 6 (from 10:40 UTC): bar N > 17,534,160 (35,068,320)
Only prime-field SL/PSL groups can be checked here (haarcheck_sl.c is prime-only, haarcheck_psl.c is PSL-only, build_haar2.py
is too slow at 3·10⁷ vertices). So pgl 47 × 169, pgl 71 × 49 (ties the bar anyway) and sl 64 × 67 (GF(64), no checker) were
stopped without a verdict.
Results so far (unsolved): sl 47 × 169 seed 1 best 6 (30k evals), seed 2 best 8 (21.6k), psl 73 × 91 best 8 (25k evals, μ 28.9),
sl 43 × 223 best 18 (12k, μ 29.5), sl 37 × 349 best 36 (9.5k, μ 28.2, stopped).
Running: sl 47 × 169 seeds 2 and 3 (3600 s), psl 73 × 91, sl 43 × 223.

### Round 6 and 7 results so far (all unsolved above the bar 17,534,160)
- sl 47 × Z169 (N 17,538,144, μ 25.4, |Fix| 47): seeds 1–4 best 6, 8, 6, 8 (30k–46k evals each, 40–60 min). Seed 5 at 10 (running).
- psl 73 × Z91 (N 17,696,952, μ 28.9, |Fix| 35): seed 1 best 6 (52k evals, 60 min), seed 2 best 11 (55k), seed 3 at 15 (running).
- sl 43 × Z223 (N 17,720,472, μ 29.5): best 12 (38k evals, 60 min).
- sl 83 × Z31 (N 17,722,824, μ 29.5): best 10–12 at 30 min (running).
- sl 37 × Z349 (N 17,664,984, μ 28.2): best 36 at 9.5k evals (stopped).
Reading: at μ ≥ 25 the success rate per 40-minute run fell well below one in five across these groups; the sl 71 × 49 success
(μ 25.3, seed 2) came from one of two seeds and was the last success. This is consistent with the STRUCTURE.md wall (cost falls
slowly past μ ≈ 25; each further +1 in μ needs several times more evaluations).

## Final state (stopped 13:16 UTC, about 5h35m of the 6-hour allowance)

**Record: 35,068,320 vertices** = 2 · |SL(2,71) × Z49|, k = 3, m = 4, f = 0 (sol file `d12D9_sl_71_49_orb3f0_s2.txt`), checked
by haarcheck_sl and haarcheck2 (both VALID). Previous record in this session chain: 34,026,720 (SL(2,41) × Z247).

Steps: 34,264,920 (psl 61 × 151) → 34,677,888 (sl 97 × 19) → 34,710,480 (psl 71 × 97) → 35,068,320 (sl 71 × 49). Table 30,001,152.

**Unsolved above the bar (N > 17,534,160), with best cost and μ, all k=3 m=4 f=0, 40–60 min each:**
- sl 47 × Z169 (N 17,538,144, μ 25.4): five seeds, best 6, 8, 6, 8, 10 (seed 3 at 46k evals).
- psl 73 × Z91 (N 17,696,952, μ 28.9): three seeds, best 6, 11, 9 (53–55k evals each).
- sl 43 × Z223 (μ 29.5): best 12 (38k evals). sl 83 × Z31 (μ 29.5): best 8 (37k evals). sl 37 × Z349 (μ 28.2): best 36 (stopped).
- Not checkable here, not run beyond one attempt: pgl 47 × Z169 (killed), sl 64 × Z67 (GF(64), killed), pgl 71 × Z49 (killed; N ties the bar).

**Ruled out / not used:** random-sample screening with orb_screen.py (≈0.5 s per sample, too slow for ~60 groups); haar_gen3-evaluator groups
(psl 43 × 439, psl 47 × 337 seed 2: slower, both stalled at cost 18).

**What I think is stuck:** above μ ≈ 25 the orbit annealing at this order is seed-dependent, roughly one solve per 3–5 runs of
40 min at μ 21–25, and none in the μ 28–30 runs. Each further gain needs a larger budget per cell, or a new group family
(for example, a PGL or GF(q) checker so pgl and sl 64 groups can be used), not more seeds of the same groups.

**What would settle it next:** (1) a PGL(2,p) × Z_n checker (haarcheck_psl-style) so pgl 47 × 169, pgl 37 × 343 and pgl 71 × 49
(tied) become usable; (2) longer runs (2–4 h) on sl 47 × 169 and psl 73 × 91 with fresh seeds; (3) a GF(2^6) checker for sl 64 × 67 (μ 25.9).

No Haar solution above 35,068,320 was found. All verified solutions are in research/frontier/sols/d12D9_*.
