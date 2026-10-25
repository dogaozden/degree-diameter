# Cell (Δ, D) = (14, 9): raise job "raise-14-9"

Session: `claude/raise-d14d9-haar-jq8m8d` (Haiku worker, 2026-10-25). Table value 95,087,738 (DS14v2, Table 4).
Bipartite Moore bound 1,767,416,562.

**Current best: 117,072,144 vertices** = 2N, N = 58,536,072 = |PSL(2,73) × Z301|, orbit search k=3, m=4, f=2
(`research/frontier/sols/d14D9_psl_73_301_orb3_s1.txt`, μ = 16.3, 4,761 evaluations, 705 s). Verified by haar_sym's
diameter check and `tools/haarcheck_psl` (VALID, 14-regular simple). sha256 of the solution file
464a608415b4794c57b07bacfe4d512976fea778b9fdb2bd4a4633e9415db38c.

Before it: **116,211,120** = 2N, N = 58,105,560 = |SL(2,59) × Z283|, orbit search k=3, m=4, f=2
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

### Wave 2 (queued by `driver.sh` from `$SP/q`, 1800 s, seed 1; the driver keeps 4 searches running)

| group | N | 2N | μ | \|Fix\| | status |
|---|---|---|---|---|---|
| psl 47 × Z1123 | 58,270,224 | 116,540,448 | 15.1 | – | running (started 07:43) |
| sl 43 × Z733 | 58,247,112 | 116,494,224 | 15.0 | – | running (started 08:09) |
| psl 49 × Z991 | 58,270,800 | 116,541,600 | 15.1 | – | queued/running |
| sl 71 × Z163 | 58,327,920 | 116,655,840 | 15.3 | 71 | **SOLVED** at 2,977 evals (1,462 s); haar_sym OK, hcsl and hc2 VALID (ecc 9 both sides). Sub-record (below 117,072,144). File `research/frontier/sols/d14D9_sl_71_163_orb3_s1.txt`, sha256 b9b6356afbf18f0ecd9f3adc67ab1e05ad13a54561bff7ee4a924c9f5bb27792. |
| psl 73 × Z301 | 58,536,072 | 117,072,144 | 16.3 | 35 | **SOLVED** at 4,761 evals (705 s); haar_sym OK, haarcheck_psl VALID. New record. |
| psl 59 × Z571 | 58,618,860 | 117,237,720 | 16.6 | – | queued |
