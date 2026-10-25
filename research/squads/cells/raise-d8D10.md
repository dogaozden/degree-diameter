# raise-d8D10: beat 7,818,096 vertices at (Δ, D) = (8, 10)

Job "raise-8-10" (Haiku worker, branch claude/raise-d8d10-record-v7wv2z, 2026-10-25).

## Starting point
- Record held: 7,818,096 vertices = 2·|SL(2,67) × Z_13| (N = 3,909,048), file
  research/frontier/sols/d8D10_sl_67_13_orb3_s12.txt (Opus squad, claude/degree-diameter-table-squad-0xgp3g).
  Table value (DS14v2 / wiki): 6,927,210. Moore bound 94,158,416.
- Re-verified in this session: research/structured/tools/hcsl (independent low-memory SL checker): VALID, ecc 10 from both sides.
- Re-found in this session: `haar_sym 8 10 60 1 8 ... sl 67 13` with ORBIT="3 2 2" solves the record order in 57 s
  (20,929 evaluations, μ ≈ 23). So the orbit ladder is reproducible and cheap at μ ≈ 23.

## Method
- research/structured/haar_sym, ORBIT="3 2 2" (k = 3 orbit-symmetric generator set, f = 2 fixed letters, m = 2 orbits;
  Δ = 2 + 3·2 = 8). Runs by tools/orbq.sh (bash tools/orbq.sh JOBS OUTDIR haar_sym). Not executable: call with bash.
- Build: `gcc -O3 -march=native -fopenmp -o haar_sym haar_sym.c -lm` in research/structured (done here).
- Checkers built here: tools/hcsl (SL), tools/hc2 (SL, second), tools/haarcheck_psl (PSL) from research/frontier and
  research/structured/tools. build_haar2.py is the reference for ≤ 20M vertices.
- Speed: ≈ 350 evaluations/s per process at N ≈ 4·10^6 (2.9 ms each).
- Target orders (tools/orb_screen.py 8 10 3909048 4400000 "3 2 2" --list): SL/PSL/PGL(2,q)×Z_n and products with
  μ = N e^(−W/N), W = 47,079,208. μ ≈ 23 at the record; μ = 31 at N ≈ 4.0M (+2.4 %); μ = 40 at N ≈ 4.08M (+4.4 %).

## Runs (4 cores, each queue one process)
| queue | group | N | μ | budget | state |
|---|---|---|---|---|---|
| A | sl 27 × Z199 | 3,911,544 | 23.2 | 1200 s (+1800 s) | running (started 07:27 UTC) |
| B | sl 37 × Z79 | 3,998,664 | 30.8 | 3600 s | running |
| C | sl 83 × Z7 | 4,001,928 | 31.1 | 3600 s | running |
| D | sl 29 × Z163 | 3,970,680 | 28.2 | 1800 s | running |
Logs: research/structured/runs/raise-d8D10/{A,B,C,D}/*.log, queue logs in runs/raise-d8D10/*.queue.log.

60-second benchmark (4 parallel, seed 1, ORBIT 3 2 2): sl 67×Z13 solved (20.9k evals); sl 83×Z7 best 6, sl 37×Z79 best 9,
psl 49×Z67 best 6 (all after ~19–23k evals).

## Results
(none yet)

## Progress log
- 07:43 UTC (≈ 930 s in): no solve yet. Best cost / evals: C sl 83×Z7 (N 4,001,928, μ 31.1) cost 1 at 2.8e5 evals;
  A sl 27×Z199 (3,911,544, μ 23.2) cost 3 at 3.1e5; B sl 37×Z79 (3,998,664, μ 30.8) cost 3 at 3.6e5; D sl 29×Z163
  (3,970,680, μ 28.2) cost 9 at 2.4e5.

## RECORD 1: sl 37 × Z79, 7,997,328 vertices (+2.3 % over 7,818,096)
- File: research/frontier/sols/d8D10_sl_37_79_orb3_s1.txt (sha256 e2dea96188f6d95b852a4d8cd90f8207eeb0447456baccf4f3ae44e6b0f890fe).
  Log: research/structured/runs/raise-d8D10/B/d8D10_sl_37_79_orb3_s1.log. ORBIT="3 2 2", μ = 30.8, 586,777 evaluations, 1,533 s.
- Checks: haar_sym full diameter check OK; orbq queue's build_haar2.py: VALID (ecc 10 both sides, 7,997,328 vertices);
  tools/hcsl: VALID; tools/hc2: VALID.
- The ladder is working above μ ≈ 30: each solve took 2–25 min, so the next rung is N > 3,998,664.
- 08:27 UTC: sl 83×Z7 seed 1 (N 4,001,928, μ 31.1) ended at 3,600 s, best cost 1, 1.09e6 evals, no solve.
  Also no solve yet: sl 83×Z7 seed 2 (best 3), pgl 83×Z7 (best 2), prod psl 9 × psl 9 × Z31 (best 6); sl 23×Z331 stopped at 25.
  Started sl 83×Z7 seed 3 (K queue). Products with a large cyclic factor (prod sl 5 sl 7 199, prod psl 5 sl 8 133) mix badly.
  The 2 sub-record runs (sl 27×Z199, sl 29×Z163) stopped: both below the record.
