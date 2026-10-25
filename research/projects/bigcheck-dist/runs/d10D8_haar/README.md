# (10,8) Haar orbit search logs (bigcheck-dist lead, 2026-10-25)

Target: a Haar graph of degree 10 and diameter 8 on more than 1,176,480 vertices (table value, not held by us).
Program research/structured/haar_sym.c (haar_sym2 from branch claude/cell-10-8-search-t6pwvg for seed 23), orbit
search k = 3, m = 3, f = 1 (`ORBIT="3 3 1"`), one thread per seed, 4 cores shared by up to 5 jobs. Cost = misses
counted by the program; a solution needs 0. No seed solved.

| group | seeds | options | time per seed (s) | best cost |
|---|---|---|---|---|
| PSL(2,23) × Z97 (N = 588,984) | 11, 12, 13 | plain, ORBW=3, ORBW=3 RESTART=1 | 1,745, 1,239, 528 | 12, 9, 10 |
| PSL(2,7) × SL(2,8) × Z7 (N = 592,704) | 21, 22 | RESTART=1 | 9,800 | 9, 10 |
| same | 23 | haar_sym2 RESTARTAFTER=2 ORBW=3 | 9,800 | 12 |
| same | 24 | plain | 8,800 | 10 |
| same | 25 | RESTART=1 | 5,200 | 9 |
| same | 26, 27, 28 | RESTART=1 | 1,650 | 14, 12, 10 |

Total on PSL(2,7) × SL(2,8) × Z7: about 48,000 thread-seconds and 6.9·10⁷ evaluations. Descents typically end at cost
12-22; the lowest was 9 (the cell-10-8 session's best is 7). So reaching 0 needs much more than the ~200 descents that
session estimated, or a different idea. Command (per seed s, time budget T):

    ORBIT="3 3 1" RESTART=1 THREADS=1 ./haar_sym 10 8 T s 8 d10D8_prod_orb3_RESTART_s<s>.txt prod psl 7 sl 8 7
