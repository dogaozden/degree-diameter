# c05: k -> hmeta cost at fixed mu (Delta = 4, 5; D = 15, 16)

Groups: Z_m x|_r Z_k, m prime = 1 mod 2k, r of order k, chosen by pickall.py with mu closest to 8 (groups.json).
Run: `env T0=8 T1=1 REHEAT=400 THREADS=1 hmeta d D secs seed 8 OUT m k r`, secs = 30 (Delta 4) or 35 (Delta 5).
"start" = the start cost hmeta prints for the random S (its initial hole count). "cost" = best cost reached.
Cost 0 = solved. Seeds 1 and 2 at Delta 4, seed 1 only at Delta 5.
Machine was loaded (4 cores, other cards), so Delta 5 got only about 82 evaluations per run instead of about 600.

## Delta = 4, D = 15 (m = the prime; N = m k; mu from pickall)
| k | m | N | mu | start (s1 / s2) | cost (s1 / s2) |
|---:|---:|---:|---:|---|---|
| 13 | 48907 | 635791 | 8.0 | 4820 / 87848 | 74 / 58 |
| 19 | 33479 | 636101 | 8.0 | 1600 / 404 | 10 / 12 |
| 31 | 20399 | 632369 | 7.5 | 32 / 554 | **0 (solved, s1, 22 s)** / 2 |
| 43 | 14879 | 639797 | 8.6 | 58 / 88 | 4 / 2 |
| 61 | 10859 | 662399 | 13.1 | 32 / 2774 | 6 / 4 |
| 97 | 6791 | 658727 | 12.3 | 16 / 280 | 6 / 6 |
| 151 | 4229 | 638579 | 8.4 | not finished (killed) | - |
k = 211, 307: no prime m in the mu window (mu grid too coarse at this N); not run.

## Delta = 4, D = 16 (m = the prime; N = m k)
| k | m | N | mu | start (s1 / s2) | cost (s1 / s2) |
|---:|---:|---:|---:|---|---|
| 13 | 134681 | 1750853 | 8.0 | 10931 / 138457 | 224 / 248 |
| 19 | 92189 | 1751591 | 8.1 | 18990 / 380 | 24 / 16 |
| 31 | 56359 | 1747129 | 7.8 | 27 / 549 | 5 / 4 |
| 43 | 40507 | 1741801 | 7.5 | 44 / 39 | 2 / 2 |
| 61 | 28793 | 1756373 | 8.4 | 16 / 1403 | 2 / 2 |
| 97 | 18043 | 1750171 | 8.0 | 16 / 115 | 1 / not finished |
k = 151, 211, 307 not finished (killed when the time box ran out).

## Delta = 5, D = 15 (seed 1 only, about 82 evaluations)
| k | mu | start | cost |
|---:|---:|---:|---:|
| 13 | 8.0 | 39136 | 3190 |
| 19 | 8.0 | 1332 | 202 |
| 31 | 8.0 | 66 | 30 |
| 43 | 8.2 | 42 | 26 |
| 61 | 8.0 | 22 | 14 |
| 97 | 8.2 | 16 | 6 |
| 151 | 7.7 | 8 | not finished |

## Delta = 5, D = 16 (seed 1 only, about 28 evaluations)
| k | mu | start | cost |
|---:|---:|---:|---:|
| 13 | 8.0 | 111602 | 9842 |
| 19 | 8.0 | 2713 | 392 |
| 31 | 8.0 | 42 | 28 |
| 43 | 8.0 | 41 | 12 |
| 61 | 8.0 | 13 | 8 |
| 97 | 8.2 | 9 | 5 |
| 151 | 8.3 | 8 | not finished |

## Reading
- k = 13 is far from random at every cell (cost 58-74 at D15, 224-248 at D16, 3190 and 9842 at Delta 5). This matches the
  beyond-d13 word-cover numbers: small k leaves many holes.
- Delta 4, D 16 is the clearest: cost falls monotonically with k (about 236, 20, 4.5, 2, 2, 1), and it is flat from k = 43 on.
  Smallest k that behaves like a random group here: about 43.
- Delta 4, D 15: k = 19 is still at about 11, k = 31 and up are at 0 to 6 (k = 31 solved in one run). Smallest random-like k:
  about 31. The k = 61 cell has mu 13, so its cost is not fully comparable.
- Delta 5: the cost falls with k at every k tried (up to 97), but the runs are too short to show a plateau. Only k >= 97 is
  a candidate for random-like, and that is unconfirmed.
- Large k (small m) did not hurt up to k = 97 at fixed mu. k = 151 and above did not finish, so that question is open.
- The start cost (random-S holes) varies by 100x between seeds (e.g. 16 to 2774), so a single random S is not a good
  measure of k. Use the best cost after a 30 s run instead.
- Valid find: (4,15) k = 31 solution, 1,264,738 vertices (N = 632,369), checked by metacheck.py: VALID. Below the director's
  1,324,798.
