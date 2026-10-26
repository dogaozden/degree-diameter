# Cell (Δ, D) = (14, 9): raise job "raise-14-9", round 3 (branch claude/raise-d14d9-haar-round3-hq51mw)

## Round 3 (started 2026-10-26, about 01:00 UTC)

**Start point.** The round-3 brief says 116,068,656, which is stale. The round-2 branch (claude/raise-d14d9-haar-resume-ita86c)
left **118,914,048** (SL(2,17) × SL(2,23), N = 59,457,024, sol `research/frontier/sols/d14D9_prod_sl_17_23_1_orb3_ORBW3_s4.txt`,
checked by `tools/haarcheck_prod.py`, VALID). So a new record needs **N > 59,457,024**. Round-2 files are copied here
unchanged, along with the round-2 tools (`research/structured/tools/`) and `research/structured/README.md`.

Plan: screen the window N in (59,457,024, 60,500,000] (mu 21.2–27) for every checkable group (SL(2,p) × Z_n, PSL(2,p) × Z_n with
p prime, SL×SL×Z_n products, all found by enumeration, not only by `orb_screen`, which caps the first factor at order 2000).
SL(2,64) × Z_229 is in the window but has no checker (prime power, single factor), so it is not run.

**Screen (RANDORB 150, k=3 m=4 f=2, 2026-10-26; the window's 20 checkable groups; `research/structured/runs/r3/screen.txt`).**
Admission test as in round 2 (p10 ≲ 40–48, raw uncovered counts):

| p10 | median | min | |Fix| | N | μ | group |
|---|---|---|---|---|---|---|
| 36 | 60 | 24 | 107 | 60,021,864 | 24.22 | sl 107 × Z49 |
| **37** | 60 | 17 | 50 | **59,548,008** | 21.37 | **psl 103 × Z109** |
| **42** | 66 | 21 | 44 | **59,562,360** | 21.45 | **psl 89 × Z169** |
| 44 | 68 | 22 | 431 | 60,117,120 | 24.83 | prod sl 3 × sl 71 × Z7 |
| **46** | 78 | 20 | 215 | **59,524,416** | 21.24 | **prod sl 3 × sl 37 × Z49** |
| 48 | 81 | 18 | 35 | 59,702,904 | 22.27 | psl 73 × Z307 |
| 50–54 | 78–87 | 8–36 | | sl 67 × Z199, psl 67 × Z397, sl 71 × Z169, prod sl 5 × sl 19 × Z73 (50), psl 83 × Z211 (52), psl 157 × Z31 (53) | 22–27 | |
| 62–158 | | | | prod sl 3 × sl 29 × Z103 (62), prod sl 3 × sl 27 × Z127 (66), prod sl 4 × sl 16 × Z247 (69), prod sl 5 × sl 13 × Z229 (90), prod sl 7 × sl 9 × Z247 (100), prod sl 5 × sl 11 × Z379 (144), prod sl 3 × sl 19 × Z367 (158) | | rejected |

**Orbit shape (negative result).** Other shapes on the two best groups, RANDORB 150: `2 6 2` (involution orbits, f = 2)
gives p10 1,024 on psl 103 × Z109 and 718 on prod sl 3 × sl 37 × Z49; `3 3 5` (f = 5) gives p10 261 and not finished on the
second. Both are far worse than `3 4 2` (p10 37 and 46). So round 3 runs `3 4 2` only.

**Runs (first batch, 3600 s each, pool of 4; `research/structured/runs/r3/spool`).** Started 2026-10-26 01:36 UTC.
psl 103 × Z109 (seed 1, plain), prod sl 3 × sl 37 × Z49 (seed 1, ORBW 3), psl 89 × Z169 (seed 1, plain),
psl 73 × Z307 (seed 1, ORBW 3). Queued: the same four groups on seed 2. Results go in the table below.

**Round-3 record: 119,048,832 vertices** = 2N, N = 59,524,416 = |SL(2,3) × SL(2,37) × Z_49| (k = 3, m = 4, f = 2, **ORBW = 3**,
seed 1, K = 8; 2,273 evaluations, 439 s, μ = 21.24, |Fix| = 215). Solution
`research/frontier/sols/d14D9_prod_sl_3_37_49_orb3_ORBW3_s1.txt`, sha256
a4d7c435a94862fc61d645d5c5283c4507d0770a695350678876ea1808bc5038. Log `runs/r3/spool/11-prod3_37_49_orbw3_s1/`.
Checks: haar_sym's full diameter check OK; `tools/haarcheck_prod.py` VALID (ecc 9 from both sides, all 119,048,832 vertices
reached); `tools/haarcheck_prod` (C, BFS on the same table) VALID; 14 distinct generators with e. The table
(`runs/r3/checks/`) is kept out of the sols folder (8 MB). orbq.sh cannot check prod solutions: UNCHECKED, checked by hand.

| 2N | N | group | seed / ORBW | solution file |
|---|---|---|---|---|
| **119,048,832** | 59,524,416 | SL(2,3) × SL(2,37) × Z49 | seed 1, ORBW=3 | `d14D9_prod_sl_3_37_49_orb3_ORBW3_s1.txt` |

Next rung: any group with N > 59,524,416. psl 103 × Z109 (N 59,548,008) and psl 89 × Z169 (59,562,360) are the two
lowest in the queue; the seed-2 job for SL(2,3)×SL(2,37)×Z49 was removed (same group, cannot raise the record).

**Baseline discrepancy (round 1 notes, kept below).** The round-2 brief says our record is 116,068,656. Round 1 (branch
claude/raise-d14d9-haar-jq8m8d, notes below) left a verified record of **117,837,720** (psl 109 × Z91, solution file
research/frontier/sols/d14D9_psl_109_91_orb3_s1.txt). This round starts from 117,837,720, so a new record needs N > 58,918,860.
Round-1 solution files and logs are copied into this branch unchanged.

## Round 2 result so far

**Current record: 118,914,048 vertices** = 2N, N = 59,457,024 = |SL(2,17) × SL(2,23)| (n = 1). Orbit search k = 3, m = 4,
f = 2, **ORBW = 3** (an uncovered fixed element weighs as much as a free orbit), seed 4, 11,545 evaluations (3,053 s,
μ = 20.86, |Fix| = 431). Solution `research/frontier/sols/d14D9_prod_sl_17_23_1_orb3_ORBW3_s4.txt`, sha256
5d6b861781901942d6feee9cec4c1b653f1eee2715496c5a39c8c4d9b13856dc. Checked by haar_sym's full diameter check and by
`tools/haarcheck_prod.py` (VALID, ecc 9 from both sides, all vertices reached, 14 distinct generators).

Round-2 records, in order (each checked the same way):

| 2N | N | group | seed / ORBW | solution file |
|---|---|---|---|---|
| 117,895,680 | 58,947,840 | SL(2,7) × SL(2,16) × Z43 | seed 2 | `d14D9_prod_sl_7_16_43_orb3_s2.txt` |
| 117,976,320 | 58,988,160 | SL(2,7) × SL(2,11) × Z133 | seed 2 | `d14D9_prod_sl_7_11_133_orb3_s2.txt` |
| 117,993,600 | 58,996,800 | SL(2,4) × SL(2,16) × Z241 | seed 2 | `d14D9_prod_sl_4_16_241_orb3_s2.txt` |
| **118,914,048** | 59,457,024 | SL(2,17) × SL(2,23) | seed 4, ORBW=3 | `d14D9_prod_sl_17_23_1_orb3_ORBW3_s4.txt` |

Seed 1 on the record groups above was stopped after a few minutes (same N, cannot raise the record).

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

## Round 2 stop (2026-10-25, about 20:40 UTC, six-hour budget)

**Final record: 118,914,048 vertices** (SL(2,17) × SL(2,23), ORBW = 3, seed 4; file above). Round 2 went from 117,837,720
to 118,914,048 (+0.9 %).

What worked: product groups SL(2,q1) × SL(2,q2) × Z_n, which round 1 never ran. Screening them with RANDORB (p10 ≲ 40)
found the solved groups quickly, and most of the solves came on the second seed. Groups at μ 18.2–18.4 solved in
785–5,400 evaluations (112–1,752 s). `ORBW=3` solved the μ = 20.9 group on its fourth seed, after seeds 1–3 without ORBW
stalled at cost 2–4.

Not solved, last state (3600 s unless noted): prod sl 5 × sl 79 × Z1 (N 59,155,200; seeds 1–3, best 8, 4, 2); prod sl 8 ×
sl 9 × Z163 (59,149,440; seeds 1–3, best 2, 2, 8); prod sl 8 × sl 49 × Z1 (59,270,400; seeds 1–5 and ORBW seed 4, best 2–8);
sl 53 × Z397 (59,083,128; best 6); prod sl 17 × sl 23 × Z1 seed 2 and seed 5 (best 4, 2); prod sl 7 × sl 11 × Z133 seed 1
(best 6). Runs stalled at cost 2–8 for 10k–15k evaluations; those are the same few uncovered orbits or fixed points.

Screened and rejected (p10 of random symmetric S above 40, or unverifiable): prod sl 4 × sl 8 × Z1951 (p10 186), prod sl 4
× sl 9 × Z1369 (230), prod sl 5 × sl 7 × Z1471 (516), prod sl 4 × sl 7 × Z2947 (834), prod sl 4 × sl 11 × Z751 (138),
prod sl 5 × sl 5 × Z4099 (2,172), prod sl 7 × sl 8 × Z349 (72), prod sl 5 × sl 11 × Z373 (114), prod sl 7 × sl 9 × Z247
(100). PSL factors (psl 81 × Z223 p10 39, prod psl 9 × psl 17 × Z67 p10 42, prod psl 7 × psl 19 × Z103 p10 42) were not run:
`haarcheck_prod.py` checks SL factors only, so a PSL solve could not be verified in this session.

Next steps, in order:
1. Any SL-only group with N > 59,457,024 and small p10: the enumeration of SL × SL × Z_n above it (all n with primes ≡ 1 mod 3)
   gives only large-n candidates, all screened poor so far. A PSL-capable checker (quotient of SL by ±1) would open the PSL
   candidates above.
2. More seeds with ORBW = 3 on the sl 17 × sl 23 and sl 8 × sl 49 groups (the ORBW runs stalled at 2–6 at the 3600 s budget).
3. Compute: the solves took 1–30 minutes, but most runs stalled, so breadth (many groups, one seed each, 900–1800 s) is the
   better allocation than long single runs.
