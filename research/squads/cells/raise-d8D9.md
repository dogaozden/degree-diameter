# raise-d8D9 round 2: beat the (8,9) record of 1,341,600 vertices

Job "raise2-8-9" (Haar worker, Haiku 5.5, 2026-10-25). Branch: claude/raise-d8d9-record-2-qz3qcj.
Round 1 (claude/raise-d8d9-record-ogr1zr, same notes file there) ended at 1,341,600 = sl 25 x Z43 (N 670,800).

## Target
- Beat N = 670,800 (2N = 1,341,600). Any valid Haar graph with N >= 670,801 counts.
- W(8,9) = 6,725,601; mu = N exp(-W/N). mu = 29.7 at N = 670,800; mu = 31.5 at N = 674,544; mu = 34.7 at N = 680,544.

## Candidate groups in the window 670,801 .. 690,000 (k = 3, ORBIT "3 2 2")
Screen: RANDORB=1000, seed 1, `haar_sym` from research/structured (branch claude/structured-search-orbit-w5dd4f).
Lower p1 is better; the solved reference sl 25 x Z43 has p1 66, min 28, median 260.

| group | N | mu | |Fix| | min | p1 | median | note |
|---|---|---|---|---|---|---|---|
| psl 47 x Z13 | 674,544 | 31.5 | 23 | 30 | 48 | 166 | ~1,080 involutions (odd D penalty); round 1 plateau at cost 5-6 |
| sl 17 x Z139 | 680,544 | 34.7 | 17 | 42 | 132 | 514 | only -I as involution; round 1 best 12 (3.4M evals) |
| prod psl 5 x psl 7 x Z67 | 675,360 | 32.0 | 8 | 84 | 120 | 1368 | round 1 best 15 |
| prod sl 4 x psl 7 x Z67 | 675,360 | 32.0 | 8 | 66 | 111 | 1113 | A5 factor, involutions |
| sl 13 x Z313 | 683,592 | 36.5 | 11 | 222 | 342 | 3120 | |
| sl 8 x Z1333 | 671,832 | 30.2 | 8 | 18966 | 25206 | 104280 | large cyclic factor: hopeless |
| sl 8 x Z1339 | 674,856 | 31.7 | 8 | 19734 | 24510 | 107706 | large cyclic factor: hopeless |
| sl 7 x Z1999 | 671,664 | 30.1 | 5 | 92898 | 110970 | 315258 | large cyclic factor: hopeless |
| sl 11 x Z511 | 674,520 | 31.5 | 11 | 552 | 786 | 11172 | cyclic 511: poor |
| sl 9 x Z937 | 674,640 | 31.6 | 17 | 6462 | 7542 | 73602 | q = 9 is divisible by 3 |
| psl 13 x Z619 | 675,948 | 32.3 | 5 | 1034 | 1356 | 12342 | |

Summary: the orbit window above 670,800 holds no SL-type group with a small cyclic factor. The only candidates with a
good tail are psl 47 x Z13 (involutions) and sl 17 x Z139 (mu 34.7). The SL-type groups with the lowest mu all have a cyclic
factor of 500 to 2,000, and their tails are 100 to 1,000 times worse. Nothing in 670,801 .. 676,000 was screened with
ORBW or RESTART before this round.

## Structures tried or ruled out (round 2)
- **k = 7, f = 1, m = 1** (Delta = 1 + 7, one free orbit of size 7 plus e). The space is only N/7 ~ 96k sets, so an
  exhaustive sample would be cheap. RANDORB=3000 showed it is hopeless: psl 13 x Z617 min 198 (|Fix| 6, mu 31.1);
  psl 7 x Z4019 min 11,382; sl 7 x Z2003 min 3,992. One orbit gives too little freedom. Do not retry.
- **Groups for k = 7 at N ~ 670k** (7 | |Q|, primes of n = 1 mod 7): only psl 13 x Z617, psl 7 x Z4019, sl 7 x Z2003,
  sl 8 x Z1373 (N 691,992, mu 41.5). All screened or too high.
- **Products SL(2,q1) x SL(2,q2) with no Z factor** in the window: none exist (checked all q <= 1300).
- **Groups with few involutions (odd D):** SL(2,q) with q odd has one involution (-I). SL(2,q) with q even (sl 8, sl 16) has
  q^2-1 unipotent involutions, each missed with probability e^(-lambda/2). sl 16 x Z163 (round 1, mu 27, best 9) fits this.
- **PSL(2,q) for odd D:** about q(q-1)/2 involutions (1,081 for q = 47), each missed with probability e^(-lambda/2) =
  0.0068 at lambda = 9.97, which is about 7 expected misses before orbit correlation. This is the likely cause of psl 47's plateau.

## Runs (round 2, 1 hour each, 1 thread, nice 5; logs and outputs in research/structured/runs/r2 on the scratch copy)
- psl 47 x Z13, ORBIT "3 2 2", ORBW=3, seed 31 (test: does ORBW fix psl's plateau?). Seed 32 stopped early to free a core.
- psl 47 x Z13, RESTART=1, seed 33: stopped early (replaced by the sl 17 runs).
- sl 17 x Z139, ORBIT "3 2 2", ORBW=3, seeds 35 and 36. sl 17 x Z139, ORBIT "3 2 2", seed 37 (default weights).

## Results, round 2 first hour (1 h each, no solve)
| run | group | N | weights | best cost | evals |
|---|---|---|---|---|---|
| s31 | psl 47 x Z13 | 674,544 | ORBW=3 | **3** | 3.84M |
| s35 | sl 17 x Z139 | 680,544 | ORBW=3 | 20 | 3.46M |
| s36 | sl 17 x Z139 | 680,544 | ORBW=3 | 30 | 3.53M |
| s37 | sl 17 x Z139 | 680,544 | default | 36 | 3.53M |

- psl 47 x Z13 with ORBW=3 beats round 1's plateau (5-6 in 3.6M evals, default weights). Cost 3 is one orbit of 3 or
  fixed elements left. This is the lead for round 2.
- sl 17 x Z139 is worse here than round 1 (best 12). Round 1 used default weights; the spread across seeds is large.
  Not pursued further.

## Next (round 2, second block)
- psl 47 x Z13, ORBW=3, seeds 41-43 at 2 h each, plus seed 44 with RESTART=1 ORBW=3.
