# Cell (Δ, D) = (14, 9): raise job "raise-14-9"

Session: `claude/raise-d14d9-haar-jq8m8d` (Haiku worker, 2026-10-25). Table value 95,087,738 (DS14v2, Table 4).
Bipartite Moore bound 1,767,416,562.

**Current best: 117,837,720 vertices** = 2N, N = 58,918,860 = |PSL(2,109) × Z91|, orbit search k=3, m=4, f=2
(`research/frontier/sols/d14D9_psl_109_91_orb3_s1.txt`, μ ≈ 18.0, 6,609 evaluations, 1,524 s). Verified by haar_sym's
diameter check and `tools/haarcheck_psl` (VALID, 14-regular simple). sha256 of the solution file
5ce28d75552724a814639d080018cd55415f673ca2330d20b7f4b8468bc76b4c.

Before it: **117,072,144** = 2N, N = 58,536,072 = |PSL(2,73) × Z301|, orbit search k=3, m=4, f=2
(`research/frontier/sols/d14D9_psl_73_301_orb3_s1.txt`, μ = 16.3, 4,761 evaluations, 705 s). Verified by haar_sym's
diameter check and `tools/haarcheck_psl` (VALID, 14-regular simple). sha256 of the solution file
464a608415b4794c57b07bacfe4d512976fea778b9fdb2bd4a4633e9415db38c.

Before that: **116,211,120** = 2N, N = 58,105,560 = |SL(2,59) × Z283|, orbit search k=3, m=4, f=2
(`research/frontier/sols/d14D9_sl_59_283_orb3_s1.txt`, μ = 14.43, 441 evaluations, 118 s). Verified by haar_sym's
diameter check, `tools/hcsl` and `tools/hc2` (both VALID, ecc 9 from both sides). sha256 of the solution file
4f5834735617679254cb0b788484feaf54082c698fa191c56d2049454fc3d661.

Starting record (this job's baseline): 116,068,656 = 2N, N = 58,034,328 = |SL(2,67) × Z193|
(`research/frontier/sols/d14D9_sl_67_193_orb3_s1.txt`, μ = 14.14, 3,409 evaluations, 1,155 s).

## Method

Orbit-symmetric Haar search (`research/structured/`, `haar_sym.c`): S = {e} ∪ (2 torus generators fixed by α) ∪ (4 free
α-orbits of size 3), α = conjugation by an order-3 element of Q times z ↦ rz on Z_n. Ladder over group orders
N = |Q| · n just above the record, screened with `tools/orb_screen.py 14 9 LO HI "3 4 2" --list`.

Model (`tools/mu_plan.py`, W(14,9) = 883,708,281): μ = N e^(−W/N). Around N = 58M, d ln μ / d ln N ≈ 1 + W/N ≈ 16, so
each +1 % in N multiplies μ by about 1.17:

| μ | N (= |G|) | 2N |
|---|---|---|
| 14.1 | 58.03 M | 116.07 M (record) |
| 16 | 58.4 M | 116.9 M |
| 20 | 59.3 M | 118.6 M |
| 25 | 60.1 M | 120.3 M |
| 30 | 60.8 M | 121.7 M |

Cost model from the record: about 170 · e^(μ/4.7) evaluations at ~0.35 s each (scaled from one solve, very rough).
Four cores, 6 h budget → about 250k evaluations in total, so μ ≈ 25–30 is the practical ceiling for this cell.

Checks: N > 10M (all cells here) use the low-memory checkers `tools/hcsl` + `tools/hc2` (SL) or `tools/haarcheck_psl`
(PSL), built from `research/frontier/haarcheck_sl.c`, `haarcheck2.c` and `research/structured/tools/haarcheck_psl.c`.
`orbq.sh` runs them automatically on any solution above 10M.

Note: `tools/orbq.sh` and `pool.sh` are not executable in this checkout; run them with `bash tools/orbq.sh JOB OUT`.

## Runs

(Log of every run; the coordinator re-checks anything listed as VALID.)

### Wave 1 (μ ≈ 14.2–14.4, seed 1, 1800 s each, 2026-10-25 07:39 UTC)

| group | N | 2N | μ | \|Fix\| | wide rows | result |
|---|---|---|---|---|---|---|
| sl 37 × Z1147 | 58,056,552 | 116,113,104 | 14.23 | 35 | yes (HW 222) | not solved: best 38, 10,241 evals in 1800 s |
| sl 31 × Z1951 | 58,061,760 | 116,123,520 | 14.25 | 29 | **no** (fallback, slower) | not solved: best 54, 8,641 evals in 1800 s |
| sl 59 × Z283 | 58,105,560 | 116,211,120 | 14.43 | 59 | yes (HW 118) | **SOLVED** at 441 evals (118 s), VALID by haar_sym, hcsl, hc2. New record. |
| psl 41 × Z1687 | 58,100,280 | 116,200,560 | 14.41 | 20 | yes (HW 241) | not solved: best 24, 9,217 evals in 1800 s |

Wave-1 read: 1 of 4 solved, and the three misses ended far from 0 (best 24–54), so a 30-minute run at μ≈14.3 is
not reliable. Solve speed depends on the group more than on μ alone. The solved group had the largest |Fix| (59).

### Waves 3 and 4 (queued by `driver2.sh` / `driver3.sh`, 1800–3600 s, seed 1)

| group | N | 2N | μ | \|Fix\| | result |
|---|---|---|---|---|---|
| psl 109 × Z91 | 58,918,860 | 117,837,720 | 18.0 | 53 | **SOLVED** at 6,609 evals (1,524 s), haar_sym OK, haarcheck_psl VALID. **New record.** |
| sl 389 × Z1 | 58,863,480 | 117,726,960 | 17.8 | 389 | **SOLVED** at 8,265 evals (3,193 s); haar_sym OK, hcsl and hc2 VALID. Sub-record (below 117,837,720). `research/frontier/sols/d14D9_sl_389_1_orb3_s1.txt`, sha256 2580f519d97bf3b299af5341e8652ef9389544af5c7e13ca3f45762dc7c7af64 |
| psl 71 × Z331 | 59,222,520 | 118,445,040 | 19.6 | – | running, best 6 at t=1423 |
| psl 59 × Z577 | 59,234,820 | 118,469,640 | 19.7 | 29 | not solved: best 4, 15,225 evals in 3600 s |
| sl 73 × Z151 | 58,730,544 | 117,461,088 | 17.1 | 71 | **SOLVED** at 833 evals (444 s); haar_sym OK, hcsl and hc2 VALID. Sub-record (below 117,837,720). `research/frontier/sols/d14D9_sl_73_151_orb3_s1.txt`, sha256 4931d658da18452d35a63dbbf4c64ed682dff9aa0cf2032812f976b91914356c |
| sl 83 × Z103 | 58,885,512 | 117,771,024 | 17.9 | 82 | **SOLVED** at 3,993 evals (1,593 s); haar_sym OK, hcsl and hc2 VALID. Sub-record (below 117,837,720). `research/frontier/sols/d14D9_sl_83_103_orb3_s1.txt`, sha256 5ff4f2dc9851bba227fedef6de8681b5d643a8c743a7b70cd3dab7f18dc06ef8 |
| psl 107 × Z97 | 59,409,396 | 118,818,792 | 20.6 | – | not solved: best 11, 8,553 evals in 3600 s |
| psl 79 × Z241 | 59,401,680 | 118,803,360 | 20.6 | – | not solved: best 6, 11,673 evals in 3600 s |
| psl 257 × Z7 | 59,410,176 | 118,820,352 | 20.6 | 128 | not solved: best 20, 9,545 evals in 3600 s |
| psl 121 × Z67 | 59,343,240 | 118,686,480 | 20.2 | – | not solved: best 6, 9,177 evals in 3600 s |
| sl 47 × Z571 | 59,256,096 | 118,512,192 | 19.8 | – | not solved: best 12, 11,105 evals in 3600 s |
| psl 47 × Z1129 | 59,204,208 | 118,408,416 | 19.5 | 23 | not solved: best 12, 12,209 evals in 3600 s |
| psl 53 × Z787 | 58,562,244 | 117,124,488 | 16.4 | 26 | not solved: best 12, 12,969 evals in 3600 s |
| psl 43 × Z1477 | 58,684,164 | 117,368,328 | 16.9 | 20 | not solved: best 18, 14,449 evals in 3600 s |
| psl 71 × Z331 | 59,222,520 | 118,445,040 | 19.6 | 35 | not solved: best 6, 8,633 evals in 3600 s |
| sl 47 × Z571 | 59,256,096 | 118,512,192 | 19.8 | – | running, best 18 |
| psl 121 × Z67 | 59,343,240 | 118,686,480 | 20.2 | – | running |
| psl 53 × Z787 | 58,562,244 | 117,124,488 | 16.4 | – | running at 3600 s budget, best 18 |
| psl 47 × Z1129 | 59,204,208 | 118,408,416 | 19.5 | – | running, best 12 |
| psl 43 × Z1477 | 58,684,164 | 117,368,328 | 16.9 | 42 | running, best 18 |
| psl 59 × Z571 | 58,618,860 | 117,237,720 | 16.6 | 29 | not solved: best 12, 6,441 evals in 1800 s |

### Wave 2 (queued by `driver.sh` from `$SP/q`, 1800 s, seed 1; the driver keeps 4 searches running)

| group | N | 2N | μ | \|Fix\| | status |
|---|---|---|---|---|---|
| psl 47 × Z1123 | 58,270,224 | 116,540,448 | 15.1 | 23 | not solved: best 18, 6,945 evals in 1800 s |
| sl 43 × Z733 | 58,247,112 | 116,494,224 | 15.0 | 41 | not solved: best 18, 5,161 evals in 1800 s |
| psl 49 × Z991 (GF(49) as x²+1) | 58,270,800 | 116,541,600 | 15.1 | 23 | not solved: best 18, 3,585 evals in 1800 s |
| sl 71 × Z163 | 58,327,920 | 116,655,840 | 15.3 | 71 | **SOLVED** at 2,977 evals (1,462 s); haar_sym OK, hcsl and hc2 VALID (ecc 9 both sides). Sub-record (below 117,072,144). File `research/frontier/sols/d14D9_sl_71_163_orb3_s1.txt`, sha256 b9b6356afbf18f0ecd9f3adc67ab1e05ad13a54561bff7ee4a924c9f5bb27792. |
| psl 73 × Z301 | 58,536,072 | 117,072,144 | 16.3 | 35 | **SOLVED** at 4,761 evals (705 s); haar_sym OK, haarcheck_psl VALID. New record. |
| psl 59 × Z571 | 58,618,860 | 117,237,720 | 16.6 | 29 | not solved: best 12, 6,441 evals in 1800 s |
