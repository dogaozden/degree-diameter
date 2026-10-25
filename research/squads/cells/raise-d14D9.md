# Cell (Δ, D) = (14, 9): raise job "raise-14-9", round 2 (branch claude/raise-d14d9-haar-resume-ita86c)

**Baseline discrepancy.** The round-2 brief says our record is 116,068,656. Round 1 (branch
claude/raise-d14d9-haar-jq8m8d, notes below) left a verified record of **117,837,720** (psl 109 × Z91, solution file
research/frontier/sols/d14D9_psl_109_91_orb3_s1.txt). This round starts from 117,837,720, so a new record needs N > 58,918,860.
Round-1 solution files and logs are copied into this branch unchanged.

## Round 2 result so far

**New record: 117,895,680 vertices** = 2N, N = 58,947,840 = |SL(2,7) × SL(2,16) × Z_43| (GF(16) as x^4+x+1), orbit search
k = 3, m = 4, f = 2, seed 2, 785 evaluations (112 s, μ = 18.19, |Fix| = 89). Solution file
`research/frontier/sols/d14D9_prod_sl_7_16_43_orb3_s2.txt`, sha256 eadaab3df868f0594d62f183c153ce9af8c35c520ed72b3c5796fad8178c8555.
Verified by haar_sym's full diameter check and by the independent `tools/haarcheck_prod.py` (ecc 9 from both sides, all
117,895,680 vertices reached, 14 distinct generators; log `research/structured/runs/r2/d14D9_prod_sl_7_sl_16_43_orb3_s2.log`).
Seed 1 on the same group was stopped after 92 s (same N, cannot raise the record). Seed 1 had reached best 6 at 657 evals.

### Round-2 runs (product groups, k = 3, m = 4, f = 2; haar_sym, 1 thread each, 3600 s unless stopped)

| group | N | μ | seed | result |
|---|---|---|---|---|
| prod sl 7 × sl 16 × Z43 | 58,947,840 | 18.19 | 1 | stopped after 165 s (same N as the record; best 3) |
| prod sl 7 × sl 16 × Z43 | 58,947,840 | 18.19 | 2 | **SOLVED** at 785 evals (112 s) → record |
| prod sl 5 × sl 79 × Z1 | 59,155,200 | 19.24 | 1 | not solved: best 8, 11,825 evals |
| prod sl 5 × sl 79 × Z1 | 59,155,200 | 19.24 | 2 | not solved: best 4, 12,833 evals |
| prod sl 4 × sl 16 × Z241 | 58,996,800 | 18.43 | 1 | not solved: best 8, 12,665 evals |
| prod sl 8 × sl 9 × Z163 | 59,149,440 | 19.21 | 1 | not solved: best 2, 8,993 evals |
| prod sl 7 × sl 11 × Z133 | 58,988,160 | 18.39 | 1 | not solved: best 6, 21,761 evals |
| prod sl 8 × sl 49 × Z1 | 59,270,400 | 19.84 | 1 | not solved: best 2, 15,385 evals |

Runs still in progress at this commit: prod sl 8 × sl 9 × Z163 seed 2, prod sl 8 × sl 49 × Z1 seed 2, prod sl 4 × sl 16 × Z241 seed 2, prod sl 7 × sl 11 × Z133 seed 2.

Observation so far: the seed-2 solve came fast (785 evals), while the other runs in the same family stalled at cost 2–8 for 10–20k evals. A seed-1 run on the record group also stalled at cost 3 after 1,137 evals, so the solve is seed luck as much as group quality.

Next target: any group with N > 58,947,840 (queue items 12–14 and the screen list below).

## Round 2 plan (started 2026-10-25, about 15:00 UTC)

- Round 1 ran the seed-1 orbit rungs over psl and sl groups from μ 14 to 20 and stopped at μ 19–21 with nothing solved.
  It never tried product groups, and never used a screen to rank groups before running them.
- **New screen (cheap).** `haar_sym` RANDORB=150 (150 random symmetric S, k=3, m=4, f=2), ~40–90 s per group. Round-1 solved
  groups all show p10 ≈ 28–33 and median ≈ 48–58 (psl 109×Z91: p10 33, median 55; sl 83×Z103: p10 28, median 54;
  sl 73×Z151: p10 32, median 58; sl 389×Z1: p10 28, median 48). Round-1 unsolved groups at μ 16.6–17.3 show p10 42–47
  and median 70–108 (psl 43×Z1477, sl 49×Z499, psl 59×Z571, sl 61×Z259 (p10 42), sl 41×Z853).
  Use p10 ≲ 35 as the admission test for a rung.
- **Product groups** (SL(2,q1) × SL(2,q2) × Z_n, no PSL factor: PSL factors add involution misses for odd D) were
  never run in round 1. Screen results (RANDORB 150; the top candidates are queued):

| group | N | μ | |Fix| | min | p10 | median | verdict |
|---|---|---|---|---|---|---|---|
| prod sl 7 × sl 16 × Z43 | 58,947,840 | 18.19 | 89 | 12 | **28** | **52** | top; seeds 1 and 2 running |
| prod sl 5 × sl 79 × Z1 | 59,155,200 | 19.24 | 467 | 16 | 38 | 66 | queued (seed 1) |
| prod sl 4 × sl 16 × Z241 | 58,996,800 | 18.43 | 44 | 17 | 48 | 75 | queued (seed 1) |
| prod sl 8 × sl 9 × Z163 | 59,149,440 | 19.21 | 161 | 20 | 42 | 78 | queued (seed 1) |
| prod sl 7 × sl 11 × Z133 | 58,988,160 | 18.39 | 71 | 26 | 44 | 92 | weak |
| prod sl 7 × sl 8 × Z349 | 59,101,056 | 18.96 | 53 | 36 | 72 | 120 | no |
| prod sl 5 × sl 11 × Z373 | 59,083,200 | 18.87 | 71 | 78 | 114 | 182 | no |
| sl 53 × Z397 | 59,083,128 | 18.87 | 53 | 24 | 54 | 94 | weak (round 1: best 6 at 2400 s) |
| sl 47 × Z571 | 59,256,096 | 19.77 | 47 | 36 | 84 | 126 | no (round 1: best 12) |

- **Verification of product solutions.** `orbq.sh` cannot check product groups ("UNCHECKED"). I added
  `tools/haarcheck_prod.py` (builds the SL(2,q) factors from the definitions, GF(q) arithmetic from the header's poly)
  and `tools/haarcheck_prod.c` (BFS on both sides, one byte per vertex). Self-test `tools/test_haarcheck_prod.py`: 80
  random small graphs, exact agreement with brute-force eccentricities, no mismatches.
- `orbq.sh` and `pool.sh` were not executable; `chmod +x` was needed to run them through `pool.sh`.
- Queue: `runs/r2/spool` (drained by `tools/pool.sh runs/r2/spool 4`), logs in `runs/r2/`.

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
| sl 49 × Z499 | 58,682,400 | 117,364,800 | 16.9 | – | not solved: best 6, 7,297 evals in 2400 s |
| sl 41 × Z853 | 58,754,640 | 117,509,280 | 17.3 | – | not solved: best 24, 6,233 evals in 2400 s |
| sl 61 × Z259 | 58,772,280 | 117,544,560 | 17.3 | – | not solved: best 6, 10,433 evals in 2400 s |
| psl 41 × Z1723 | 59,340,120 | 118,680,240 | 20.2 | – | not solved: best 42, 6,817 evals in 2400 s |
| psl 43 × Z1483 | 58,922,556 | 117,845,112 | 18.1 | 20 | not solved: best 42, 7,505 evals in 2400 s |
| sl 53 × Z397 | 59,083,128 | 118,166,256 | 18.9 | – | not solved: best 6, 7,601 evals in 2400 s |
| psl 49 × Z1009 | 59,329,200 | 118,658,400 | 20.2 | – | queued, cancelled before start (μ ≈ 20 with the weakest prospects of the queue) |
| sl 47 × Z571 | 59,256,096 | 118,512,192 | 19.8 | – | not solved: best 12, 11,105 evals in 3600 s |
| psl 121 × Z67 | 59,343,240 | 118,686,480 | 20.2 | – | not solved: best 6, 9,177 evals in 3600 s |
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

## Status at stop (2026-10-25, about 13:15 UTC, session budget reached)

**Final record in this session: 117,837,720 vertices** (psl 109 × Z91, sha256 5ce28d75…, verified by haar_sym and
haarcheck_psl). The start was 116,068,656; the session added +1.5 % (1,769,064 vertices).

Verified sub-records, all below the record and kept in `research/frontier/sols/`: sl 71 × Z163 (116,655,840),
sl 389 × Z1 (117,726,960), sl 83 × Z103 (117,771,024), sl 73 × Z151 (117,461,088), and psl 73 × Z301 (117,072,144,
which was a record at the time). The earlier sl 59 × Z283 record (116,211,120) is kept too.

**Why I stopped.** The 6-hour budget ran out. Last hour of runs at μ = 19–21: none solved (best costs 4–48). Rungs at
μ = 16–18 gave 4 solves out of about 15 attempts; solves came fast (hundreds to a few thousand evaluations) or not at all
within 1800–3600 s. Going above μ ≈ 18 in this cell needs much more compute (orbit method: evals ≈ C·e^(μ/4.7) with a
large spread between groups). The next worthwhile rung is psl or sl with N ≈ 58.9–59.3 M and |Fix| small
(psl 109 × Z91 had |Fix| = 53, sl 389 × Z1 had 389, so |Fix| alone does not decide it). Not tried: other seeds on
psl 109 × Z91 family or on the sub-record groups at higher N, and the SL(3,q) or route-chart ideas in SIZE_LAW.
