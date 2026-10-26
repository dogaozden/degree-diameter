# Cell (13,8): raise the Haar record (job raise-13-8)

Record to beat: 6,814,080 vertices = 2N with N = |SL(2,64) x Z_13| = 3,407,040 (13-regular Haar graph, k = 3, m = 4,
f = 1, conjugation orbits; file research/frontier/sols/d13D8_sl_64_13_orb3_s1.txt). Table value 5,314,680.
Moore bound 78,178,490. Model: W(13,8) = 39,089,245, mu = N exp(-W/N) (SIZE_LAW, mu_plan.py); the record has mu = 35.5.

Branch: claude/raise-d13d8-haar-7qqnoz. Working notes: this file (kept current); scratch in the session scratchpad.

## Plan

- Groups of order N in (3,407,040, ~3,500,000] whose Z-factor is 1 or has only primes = 1 mod 3 (so that z -> rz,
  r of order 3, is available). Each +1 % in N is +1 % in vertices; mu grows about 13 % per +1 % in N here, so the
  reachable window is a few percent above the record.
- Screen with RANDORB (orb_screen.py, 300 samples), then anneal the best candidates on 4 cores (THREADS=1).
- Verify with build_haar2.py (< 20M vertices), the low-memory checkers above.

## Candidate orders (k = 3 compatible), 3,407,041 .. 3,480,000

orb_screen.py 13 8 3407041 3480000 "3 4 1" --samples 300 (k = 3 compatible n only; 35 candidates; ranked by (p1+p10)/2):

| rank | N | 2N | mu | fix | p1 | p10 | median | group | mu_A = mu/3 + fix e^(-lambda/3) |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 3,450,720 | 6,901,440 | 41.5 | 77 | 23 | 36 | 53 | sl 79 7 | 15.6 |
| 2 | 3,416,952 | 6,833,904 | 36.8 | 41 | 27 | 33 | 51 | sl 43 43 | 13.2 |
| 3 | 3,427,200 | 6,854,400 | 38.2 | 89 | 25 | 38 | 59 | prod sl 5 sl 16 7 | 14.7 |
| 4 | 3,442,800 | 6,885,600 | 40.4 | 149 | 25 | 38 | 55 | sl 151 1 | 16.9 |
| 5 | 3,416,952 | 6,833,904 | 36.8 | 41 | 27 | 37 | 59 | pgl 43 43 | 13.2 |
| 6 | 3,450,720 | 6,901,440 | 41.5 | 77 | 27 | 37 | 59 | pgl 79 7 | 15.6 |
| 7 | 3,437,280 | 6,874,560 | 39.6 | 17 | 24 | 42 | 66 | prod psl 7 psl 11 31 | 13.6 |
| 8 | 3,453,840 | 6,907,680 | 42.0 | 80 | 29 | 39 | 60 | psl 81 13 | 15.8 |
| 9 | 3,407,520 | 6,815,040 | 35.5 | 14 | 30 | 42 | 66 | psl 31 229 | 12.1 |
| 10 | 3,412,800 | 6,825,600 | 36.2 | 53 | 30 | 42 | 74 | prod sl 5 psl 9 79 | 13.2 |
| 11 | 3,447,360 | 6,894,720 | 41.0 | 161 | 32 | 40 | 64 | prod sl 8 sl 19 1 | 17.3 |
| 12 | 3,476,496 | 6,952,992 | 45.5 | 23 | 30 | 42 | 69 | psl 47 67 | 15.7 |
| 13 | 3,412,800 | 6,825,600 | 36.2 | 53 | 28 | 46 | 78 | prod psl 5 sl 9 79 | 13.2 |
| 14 | 3,412,800 | 6,825,600 | 36.2 | 53 | 30 | 46 | 77 | prod sl 4 sl 9 79 | 13.2 |
| 15 | 3,430,224 | 6,860,448 | 38.6 | 125 | 31 | 46 | 70 | prod psl 3 psl 83 1 | 15.7 |
| 16 | 3,447,360 | 6,894,720 | 41.0 | 80 | 33 | 44 | 66 | prod psl 9 sl 8 19 | 15.5 |
| 17 | 3,443,328 | 6,886,656 | 40.4 | 17 | 30 | 49 | 79 | prod psl 7 sl 7 61 | 13.9 |
| 18 | 3,446,940 | 6,893,880 | 41.0 | 14 | 30 | 51 | 78 | psl 29 283 | 14.0 |
| 19 | 3,436,752 | 6,873,504 | 39.5 | 23 | 34 | 51 | 81 | sl 23 283 | 13.7 |
| 20 | 3,463,200 | 6,926,400 | 43.4 | 35 | 36 | 49 | 81 | prod psl 3 psl 25 37 | 15.3 |

Reference, the record group SL(2,64) x Z_13 (150 samples, same screen): N = 3,407,040, mu = 35.5, fix = 62, p1 = 18, p10 = 30, median = 49; mu_A = 13.2.

The screen ranks random symmetric S only. mu_A is the model's effective mean (SIZE_LAW / BEYOND_RANDOM): it predicts the anneal's difficulty, and the random-sample stats are noisy, so the anneal decides.

## Log

- 08:06 UTC: binaries built (research/structured/haar_sym, haar_fast). Screen above (35 candidates).
- 08:10 UTC: round 1 started, ORBIT="3 4 1", THREADS=1, 7200 s, seed 1, four groups:
  sl 43 x Z43, prod psl 7 psl 11 x Z31, psl 31 x Z229, prod sl 5 sl 16 x Z7.
- 10:10 UTC: round 1 ended for sl 43 x Z43 (best 3, 838,105 evals) and prod psl 7 psl 11 x Z31 (best 3, 944,737 evals).
  psl 31 x Z229 and prod sl 5 sl 16 x Z7 still running (end ~10:12). No solution in round 1.
- 10:10 UTC: round 2 started, ORBIT="3 4 1" ORBW=3 (uncovered fixed element weighs 3), seed 2, 7200 s:
  sl 43 x Z43 and prod psl 7 psl 11 x Z31.
- Live logs are not tracked (ignored, runs/raise13/*.log); checkpoints are committed as *.snap.log.
- 10:10 UTC: round 1 ended for psl 31 x Z229 (best 3, 1,234,185 evals) and prod sl 5 sl 16 x Z7 (best 4, 1,019,801 evals).
  No solution in round 1 (all four groups).
- 10:12 UTC: round 2b started, ORBIT="3 4 1" ORBW=3, seed 2, 7200 s: psl 31 x Z229 and prod sl 5 sl 16 x Z7.
  Round 2 now has four runs (two started 10:10, two started 10:12).
- 10:19 UTC: SOLVED. Round 2 (ORBW=3, seed 2) on sl 43 x Z43 (N = 3,416,952): cost 0 after 32,177 evaluations (267 s).
  Solution research/frontier/sols/d13D8_sl_43_43_orb3_ORBW3_s2.txt, 6,833,904 vertices (+19,824 over 6,814,080, +0.29 %).
  Checks: haar_sym full diameter check OK; haarcheck_sl VALID; build_haar2.py VALID (13-regular, no duplicate edges,
  edge-list sha256 cd5d3aedbaa36ae1d5431dd927395ea2219c1e24c692db2e6776144767331b4f). Check text in runs/raise13/*.check.txt.
  Awaiting the coordinator's independent re-check.
- Round 2 still running for prod psl 7 psl 11 x Z31, psl 31 x Z229, prod sl 5 sl 16 x Z7 (ORBW=3, seed 2).
- 10:18 UTC: psl 31 x Z229 (N = 3,407,520, below the new record) stopped after RESULT best 6; not useful any more.
  Freed cores: sl 79 x Z7 (N = 3,450,720, mu 41.5, fix 77) and psl 81 x Z13 (N = 3,453,840, mu 42.0, fix 80), both
  ORBW=3 seed 2, 2 h. Still running: prod psl 7 psl 11 x Z31 (N = 3,437,280) and prod sl 5 sl 16 x Z7 (N = 3,427,200),
  ORBW=3 seed 2. Any N above 3,416,952 beats the new record 6,833,904.
- 11:11 UTC (about 1 h into round 2b): no solution. Best costs: prod psl 7 psl 11 x Z31 3 (4.7e5 evals),
  prod sl 5 sl 16 x Z7 6 (4.8e5), sl 79 x Z7 4 (3.9e5), psl 81 x Z13 6 (2.7e5). Runs end about 12:12 UTC.
- 12:11 UTC: round 2b results (ORBW=3, seed 2, 2 h): prod psl 7 psl 11 x Z31 best 3 (905,553 evals), prod sl 5 sl 16 x Z7
  best 6 (956,425 evals). No solution. sl 79 x Z7 (best 4) and psl 81 x Z13 (best 6) end about 12:18 UTC.
  Round 3 started 12:11 UTC: prod sl 5 sl 16 x Z7, ORBW=3, seed 3, 5400 s (the only fresh run on a candidate
  that beats 3,416,952 in N with a seed not yet tried).
- 12:18 UTC: round 2b, last results: psl 81 x Z13 best 6 (603,425 evals), sl 79 x Z7 best 3 (875,969 evals). No solution.
- 12:19 UTC: round 3 seeds, ORBW=3, 5400 s each: sl 79 x Z7 (seed 3) and prod psl 7 psl 11 x Z31 (seed 3), plus
  prod sl 5 sl 16 x Z7 (seed 3, started 12:11). All end by about 13:45 UTC, leaving time for the write-up before 14:06.

## Final status (13:50 UTC, end of the 6-hour budget)

Record: **6,833,904 vertices**, SL(2,43) x Z_43 (N = 3,416,952), k = 3, m = 4, f = 1, conjugation orbits, ORBW=3,
seed 2 (cost 0 after 32,177 evaluations, 267 s). Solution: research/frontier/sols/d13D8_sl_43_43_orb3_ORBW3_s2.txt.
Checks: haar_sym full diameter check OK; haarcheck_sl VALID; build_haar2.py VALID (edge-list sha256 cd5d3aed...).

All anneal runs (ORBIT="3 4 1", THREADS=1; every RESULT line is in the snapshot logs under runs/raise13/):

| group | N | mu | round | seed | ORBW | best cost | evals |
|---|---|---|---|---|---|---|---|
| sl 43 x Z43 | 3,416,952 | 36.8 | 1 | 1 | 1 | 3 | 8.4e5 |
| prod psl 7 psl 11 x Z31 | 3,437,280 | 39.6 | 1 | 1 | 1 | 3 | 9.4e5 |
| psl 31 x Z229 | 3,407,520 | 35.5 | 1 | 1 | 1 | 3 | 1.2e6 |
| prod sl 5 sl 16 x Z7 | 3,427,200 | 38.2 | 1 | 1 | 1 | 4 | 1.0e6 |
| sl 43 x Z43 | 3,416,952 | 36.8 | 2 | 2 | 3 | **0 (solved)** | 3.2e4 |
| psl 31 x Z229 | 3,407,520 | 35.5 | 2 | 2 | 3 | 6 | 7e4 |
| prod psl 7 psl 11 x Z31 | 3,437,280 | 39.6 | 2 | 2 | 3 | 3 | 9.1e5 |
| prod sl 5 sl 16 x Z7 | 3,427,200 | 38.2 | 2 | 2 | 3 | 6 | 9.6e5 |
| sl 79 x Z7 | 3,450,720 | 41.5 | 2 | 2 | 3 | 3 | 8.8e5 |
| psl 81 x Z13 | 3,453,840 | 42.0 | 2 | 2 | 3 | 6 | 6.0e5 |
| prod sl 5 sl 16 x Z7 | 3,427,200 | 38.2 | 3 | 3 | 3 | 3 | 7.5e5 |
| sl 79 x Z7 | 3,450,720 | 41.5 | 3 | 3 | 3 | 3 | 6.8e5 |
| prod psl 7 psl 11 x Z31 | 3,437,280 | 39.6 | 3 | 3 | 3 | 3 | 7.3e5 |

Reading: the one solve came from ORBW=3 (fixed-point weight) on the group whose default-weight runs stalled at
cost 3 for two hours. Other groups stalled at cost 3-6 after 6e5-1.2e6 evaluations with either weighting. The
next rung (N in (3,416,952, 3,450,000]) needs about 10x the evaluations we spent, by the mu-rule. Not reached
within the 6-hour budget.

Stopped: psl 31 x Z229 (N below the new record, so it could not help after the solve).

---

# Round 3 (job raise3-13-8, branch claude/raise-13-8-haar-round3-bsayr9)

Record to beat: **6,999,552 vertices** = 2N with N = |SL(2,7) x SL(2,7) x Z_31| = 3,499,776, order-6 symmetry
alpha(x1, x2, z) = (c x2 c^-1, x1, 6z), c of order 3 (ASWAPC=1, AR=6, ORBIT="6 2 1"). Found by another session on
branch claude/thm-order2-symmetry-gap-4e2nmi (research/theorems/ORDER2.md §5.2, file
research/frontier/sols/d13D8_prod_sl_7_sl_7_31_orb6swc_s2.txt). The round-2 record 6,833,904 (k = 3 conjugation on
SL(2,43) x Z43) is superseded.

## What the record tells us

- Order 6 with a swap (swap of the two factors composed with conjugation of order 3) halves the clump term and
  solved at mu = 49.4, where order-3 orbit anneals had stalled at mu ~ 37 (round 2 of this cell: 13 anneals with k = 3,
  one solve, at N = 3,416,952; none above it).
- The solver is `research/theorems/order2/src/haar_order2.c` (build: `gcc -O3 -march=native -fopenmp -o haar_order2
  src/haar_order2.c -lm`). Calibration: the record group, ORBIT="6 2 1" ASWAPC=1 AR=6, random symmetric S: min 35,
  p10 64, median 141 (200 samples, 2 s). The branch's seed 2 solved in 131,625 evaluations (741 s).
- The Frobenius order-6 route at N = 3,669,120 (SL(2,64) x Z14, z -> 3z) screens far worse (random min 70, p10 130,
  median 737) and is dropped. Other earlier even-order leads at (13,8): SL(2,8)^2 x Z14 (best 13-18 in 6 seeds),
  PSL(2,13)^2 x Z3 (best 8 and 21 in 2 seeds, 1,000+ s each, from ORDER2 §6b).

## Candidate screen (round 3)

`ORBIT="6 2 1" ASWAPC=1 AR=r RANDORB=200 haar_order2 13 8 1 1 8 /dev/null prod X X n` for every swap-type group
(X x X x Z_n, |X|^2 n in (3,499,776, 3.7M]) and each admissible multiplier r (r^6 = 1 mod n; the three with the
fewest fixed points tried). Record group for reference: min 35, p10 64, median 141, mu 49.4, fix 5.

| group | n | AR | N | 2N | mu | fix | min | p10 | median |
|---|---|---|---|---|---|---|---|---|---|
| sl 5 x sl 5 | 244 | 75 | 3,513,600 | 7,027,200 | 51.78 | 11 | 77 | 262 | 5029 |
| sl 5 x sl 5 | 244 | 47 | 3,513,600 | 7,027,200 | 51.78 | 11 | 398 | 934 | 7631 |
| sl 5 x sl 5 | 244 | 135 | 3,513,600 | 7,027,200 | 51.78 | 11 | 394 | 1113 | 7685 |
| sl 5 x sl 5 | 245 | 19 | 3,528,000 | 7,056,000 | 54.41 | 5 | 124 | 210 | 1502 |
| sl 5 x sl 5 | 245 | 129 | 3,528,000 | 7,056,000 | 54.41 | 5 | 90 | 230 | 1539 |
| sl 5 x sl 5 | 245 | 79 | 3,528,000 | 7,056,000 | 54.41 | 5 | 151 | 304 | 2036 |
| sl 5 x sl 5 | 247 | 30 | 3,556,800 | 7,113,600 | 60.00 | 5 | 100 | 164 | 481 |
| sl 5 x sl 5 | 247 | 49 | 3,556,800 | 7,113,600 | 60.00 | 5 | 83 | 166 | 501 |
| sl 5 x sl 5 | 247 | 12 | 3,556,800 | 7,113,600 | 60.00 | 5 | 250 | 506 | 6331 |
| sl 5 x sl 5 | 248 | 99 | 3,571,200 | 7,142,400 | 62.97 | 11 | 74 | 311 | 6075 |
| sl 5 x sl 5 | 248 | 67 | 3,571,200 | 7,142,400 | 62.97 | 11 | 215 | 591 | 6099 |
| sl 5 x sl 5 | 248 | 87 | 3,571,200 | 7,142,400 | 62.97 | 11 | 229 | 1075 | 18042 |
| psl 13 x psl 13 | 3 | 2 | 3,577,392 | 7,154,784 | 64.29 | 5 | 52 | 91 | 163 |
| psl 7 x psl 7 | 127 | 20 | 3,584,448 | 7,168,896 | 65.82 | 2 | 66 | 144 | 373 |
| psl 7 x psl 7 | 127 | 19 | 3,584,448 | 7,168,896 | 65.82 | 2 | 333 | 579 | 2262 |
| psl 7 x psl 7 | 127 | 107 | 3,584,448 | 7,168,896 | 65.82 | 2 | 409 | 606 | 2251 |
| sl 7 x sl 7 | 32 | 15 | 3,612,672 | 7,225,344 | 72.23 | 11 | 224 | 623 | 13095 |
| sl 7 x sl 7 | 32 | 31 | 3,612,672 | 7,225,344 | 72.23 | 11 | 820 | 2862 | 150325 |
| sl 9 x sl 9 | 7 | 3 | 3,628,800 | 7,257,600 | 76.13 | 17 | 50 | 109 | 230 |
| psl 9 x psl 9 | 28 | 3 | 3,628,800 | 7,257,600 | 76.13 | 17 | 82 | 153 | 1018 |
| psl 9 x psl 9 | 28 | 19 | 3,628,800 | 7,257,600 | 76.13 | 17 | 57 | 153 | 1042 |
| sl 9 x sl 9 | 7 | 4 | 3,628,800 | 7,257,600 | 76.13 | 17 | 106 | 158 | 343 |
| sl 9 x sl 9 | 7 | 2 | 3,628,800 | 7,257,600 | 76.13 | 17 | 113 | 159 | 375 |
| psl 9 x psl 9 | 28 | 11 | 3,628,800 | 7,257,600 | 76.13 | 17 | 133 | 220 | 1451 |
| sl 5 x sl 5 | 252 | 23 | 3,628,800 | 7,257,600 | 76.13 | 11 | 137 | 449 | 48747 |
| sl 5 x sl 5 | 252 | 11 | 3,628,800 | 7,257,600 | 76.13 | 11 | 194 | 572 | 49366 |
| sl 5 x sl 5 | 252 | 47 | 3,628,800 | 7,257,600 | 76.13 | 11 | 176 | 743 | 59844 |
| psl 7 x psl 7 | 129 | 80 | 3,640,896 | 7,281,792 | 79.17 | 2 | 90 | 166 | 565 |
| psl 7 x psl 7 | 129 | 50 | 3,640,896 | 7,281,792 | 79.17 | 2 | 66 | 188 | 602 |
| psl 7 x psl 7 | 129 | 92 | 3,640,896 | 7,281,792 | 79.17 | 2 | 122 | 288 | 744 |
| sl 5 x sl 5 | 254 | 147 | 3,657,600 | 7,315,200 | 83.53 | 11 | 185 | 518 | 8420 |
| sl 5 x sl 5 | 254 | 19 | 3,657,600 | 7,315,200 | 83.53 | 11 | 1250 | 3252 | 35227 |
| sl 5 x sl 5 | 254 | 107 | 3,657,600 | 7,315,200 | 83.53 | 11 | 1190 | 3495 | 34191 |
| psl 7 x psl 7 | 130 | 49 | 3,669,120 | 7,338,240 | 86.65 | 5 | 78 | 217 | 2656 |
| psl 7 x psl 7 | 130 | 29 | 3,669,120 | 7,338,240 | 86.65 | 5 | 139 | 250 | 4050 |
| psl 7 x psl 7 | 130 | 9 | 3,669,120 | 7,338,240 | 86.65 | 5 | 118 | 258 | 4047 |
| sl 7 x sl 7 | 33 | 10 | 3,725,568 | 7,451,136 | 103.40 | 17 | 313 | 635 | 13124 |
| sl 7 x sl 7 | 33 | 32 | 3,725,568 | 7,451,136 | 103.40 | 5 | 776 | 1805 | 108968 |
| sl 7 x sl 7 | 33 | 23 | 3,725,568 | 7,451,136 | 103.40 | 65 | 2927 | 6680 | 356849 |
| sl 7 x sl 7 | 34 | 33 | 3,838,464 | 7,676,928 | 145.04 | 11 | 1067 | 4235 | 389327 |

Reading: min/p10/median are raw uncovered counts over random symmetric S. Rows with median in the thousands (large
cyclic factor, poor mixing: SL(2,5) x Z_n with n ≥ 245 for most r, SL(2,7) x Z_32, Z_33, Z_34) are not worth
annealing. Z_125, Z_131 and Z_255 and up are broken (min in the hundreds of thousands).

Chosen for round 3 (first hour, one core each, THREADS=1, seed 11):

| run | group | N | 2N | mu | AR | screen min / p10 / median |
|---|---|---|---|---|---|---|
| psl13x3_s11 | PSL(2,13)^2 x Z3 | 3,577,392 | 7,154,784 | 64.3 | 2 | 52 / 91 / 163 |
| sl9x7_s11 | SL(2,9)^2 x Z7 | 3,628,800 | 7,257,600 | 76.1 | 3 | 50 / 109 / 230 |
| psl7x127_s11 | PSL(2,7)^2 x Z127 | 3,584,448 | 7,168,896 | 65.8 | 20 | 66 / 144 / 373 |
| sl5x244_s11 | SL(2,5)^2 x Z244 | 3,513,600 | 7,027,200 | 51.8 | 75 | 77 / 262 / 5029 |

Run script: research/structured/runs/raise13r3/run1.sh (usage: `run1.sh TAG SECS SEED AR prod X X n`). Logs, best-S
files and solutions are in research/structured/runs/raise13r3/.

## Round 3, first hour (results, 02:31 UTC)

Every run: haar_order2, ORBIT="6 2 1", ASWAPC=1, THREADS=1, 3600 s. No solution.

| run | group | N | AR | best cost | evals |
|---|---|---|---|---|---|
| psl13x3_s11 | PSL(2,13)^2 x Z3 | 3,577,392 | 2 | 12 | 2.96e5 |
| psl7x127_s11 | PSL(2,7)^2 x Z127 | 3,584,448 | 20 | 18 | 5.04e5 |
| sl9x7_s11 | SL(2,9)^2 x Z7 | 3,628,800 | 3 | 25 | 5.42e5 |
| sl5x244_s11 | SL(2,5)^2 x Z244 | 3,513,600 | 75 | 35 | 4.87e5 |

Reading: no candidate got near 0. The record group (SL(2,7)^2 x Z31) solved at 1.3e5 evaluations (seed 2 of 8).
The screen medians predicted this ordering only loosely. Logs are in research/structured/runs/raise13r3/.

Second wave (started 02:33 UTC, 3600 s each): PSL(2,13)^2 x Z3 with seed 13 (plain), PSL(2,13)^2 x Z3 with OSTAB=1
seed 12, SL(2,5)^2 x Z247 (AR 30, untried), PSL(2,9)^2 x Z28 (AR 19, untried).

## Round 3, second wave (finished 03:31 UTC unless noted)

| run | group | N | variant | best cost | evals |
|---|---|---|---|---|---|
| psl13x3_s13 | PSL(2,13)^2 x Z3 | 3,577,392 | plain, seed 13 | 13 | 2.9e5 |
| psl13x3_ostab_s12 | PSL(2,13)^2 x Z3 | 3,577,392 | OSTAB=1, seed 12 | 18 | 2.9e5 |
| psl9x28_s11 | PSL(2,9)^2 x Z28 | 3,628,800 | plain, AR 19 | 27 | 3.8e5 |
| sl5x247_s11 | SL(2,5)^2 x Z247 | 3,556,800 | plain, AR 30 | 22 | 4.4e5 |

Third wave (started 03:35 UTC, 3600 s): PSL(2,13)^2 x Z3 plain seed 14; PSL(2,13)^2 x Z3 OSTAB=1 seed 15;
SL(2,9)^2 x Z7 OSTAB=1 seed 12; PSL(2,7)^2 x Z129 plain seed 11 (AR 50, untried before; started 03:30).

Running tally after 14 anneals above the record: no solution. Best costs by group: PSL(2,13)^2 x Z3 12, 13, 18;
SL(2,5)^2 x Z247 22; SL(2,9)^2 x Z7 25; PSL(2,9)^2 x Z28 27; PSL(2,7)^2 x Z127 18; SL(2,5)^2 x Z244 35.

## Round 3, third wave (results 04:31 UTC, PSL(2,13)^2 x Z3 seed 16 still running)

| run | group | variant | best cost | evals |
|---|---|---|---|---|
| psl7x129_s11 | PSL(2,7)^2 x Z129 | plain, AR 50 | 24 | 4.98e5 |
| psl13x3_s14 | PSL(2,13)^2 x Z3 | plain, seed 14 | **6** | 3.03e5 |
| psl13x3_ostab_s15 | PSL(2,13)^2 x Z3 | OSTAB=1, seed 15 | 12 | 3.0e5 |
| sl9x7_ostab_s12 | SL(2,9)^2 x Z7 | OSTAB=1, seed 12 | 19 | 5.4e5 |

Best cost 6 on PSL(2,13)^2 x Z3 (seed 14) is the closest any candidate has come. Fourth wave (04:33 UTC, 3600 s):
PSL(2,13)^2 x Z3 plain, seeds 17, 18, 19 (plus seed 16 from 04:06, still running).

## Round 3, final status (06:35 UTC; 5 h 10 min of the 6 h budget used)

**No solution above the record of 6,999,552 vertices.** 20 anneals (haar_order2, ORBIT="6 2 1", ASWAPC=1, one hour
each, THREADS=1) on candidate groups with N in (3,513,600 .. 3,640,896]. None reached cost 0.

| group | N | 2N | runs | best cost over runs |
|---|---|---|---|---|
| PSL(2,13)^2 x Z3, AR 2 | 3,577,392 | 7,154,784 | 9 (5 plain, 2 OSTAB=1 w/ seed 12/15/22, see below) | **6** (seeds 14 and 21), then 11, 12, 12, 12, 13, 13, 14, 14 |
| PSL(2,7)^2 x Z127, AR 20 | 3,584,448 | 7,168,896 | 2 | **6** (seed 12), 18 (seed 11) |
| PSL(2,7)^2 x Z129, AR 50 | 3,640,896 | 7,281,792 | 1 | 24 |
| SL(2,9)^2 x Z7, AR 3 | 3,628,800 | 7,257,600 | 2 | 19 (OSTAB=1), 25 (plain) |
| PSL(2,9)^2 x Z28, AR 19 | 3,628,800 | 7,257,600 | 1 | 27 |
| SL(2,5)^2 x Z247, AR 30 | 3,556,800 | 7,113,600 | 1 | 22 |
| SL(2,5)^2 x Z244, AR 75 | 3,513,600 | 7,027,200 | 1 | 35 |

Notes on the search:
- The group with the closest runs is PSL(2,13)^2 x Z3 (screen p10 91, record group p10 64), with several seeds at
  cost 6–14. Its OSTAB=1 variant was not better than plain (best 12 against 6–14).
- The record group (SL(2,7)^2 x Z31) solved at about 1.3e5 evaluations on 1 of 8 seeds. The candidate groups here got
  2.5–5e5 evaluations per run and did not solve in 20 tries. Under the effort law the next rung's success rate per run
  is therefore well under 5 %; the cell did not move with these methods in this budget.
- Rejected before annealing: SL(2,64) x Z14 with the Frobenius order-6 map (random min 70, far worse than Z13); swap
  groups with large cyclic factors or broken mixing (SL(2,5)^2 x Z245 and up, PSL(2,7)^2 x Z125, SL(2,7)^2 x Z32–34).

Stopped here: the cell is not solved; compute is the constraint. Next step for a later session: many more seeds of
PSL(2,13)^2 x Z3 (6 was reached twice) and PSL(2,7)^2 x Z127 (6 once) on a longer budget, with the same screen.
