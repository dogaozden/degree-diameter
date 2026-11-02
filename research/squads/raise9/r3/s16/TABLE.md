# s16 table: (16,9), beat 348,207,600. Bar N >= 174,103,801. Random symmetric S (haar_big0 RANDORB, THREADS=1)
Cost = uncovered count of random ORBIT-symmetric S (lower is better; 0 = solution). Median/mu = ratio of median to size-law mu.
Script: run.sh (wrapper of haar_big0 16 9 60 <seed> 1 /dev/null <group>); raw output in raw.log.

| group | ORBIT | mu | samples (seed) | min | p10 | median | median/mu |
|---|---|---:|---|---:|---:|---:|---:|
| SL(2,101) x Z169 (current) | 3 5 1 | 24.61 | 4 (11) | 42 | 42 | 54 | 2.2 |
| SL(2,101) x Z169 (current) | 3 5 1 | 24.61 | 10 (22) | 36 | 52 | 60 | 2.4 |
| SL(2,101) x Z169 (current) | 3 4 4 | 24.61 | 10 (28) | 60 | 66 | 96 | 3.9 |
| SL(2,157) x Z45 | 3 5 1 | 24.69 | 10 (21) | 60 | 74 | 144 | 5.8 |
| SL(2,139) x Z65 | 3 5 1 | 25.71 | 10 (23) | 70 | 70 | 82 | 3.2 |
| SL(2,89) x Z248 | 3 5 1 | 26.34 | 10 (24) | 62 | 82 | 128 | 4.9 (one sample huge, mean 1.7e7) |
| SL(2,83) x Z305 | 3 5 1 | 25.25 | 10 (25) | 62 | 62 | 98 | 3.9 |
| PSL(2,157) x Z90 | 3 5 1 | 24.69 | 10 (29) | 90 | 104 | 155 | 6.3 |
| PSL(2,179) x Z61 | 5 3 1 | 26.62 | 10 (26) | 51 | 61 | 91 | 3.4 |
| PSL(2,109) x Z271 | 5 3 1 | 28.02 | 10 (27) | 51 | 56 | 79 | 2.8 |
| PSL(2,139) x Z131 | 5 3 1 | 29.21 | 10 (33) | 39 | 61 | 89 | 3.0 |

Anneal (haar_big0, K = 4, THREADS = 1, from random S):
- SL(2,101) x Z169, ORBIT 3 5 1, 90 s (seed 31): best 32 after 20 evaluations (5 steps). Saved ref_sl101_169_k3.txt.best (not solved).
- PSL(2,109) x Z271, ORBIT 5 3 1, 80 s (seed 32): best 31 after 17 evaluations (4 steps). Saved psl109_271_k5.txt.best (not solved).

Notes: ORBIT k = 5 works in haar_big0 (choose_alpha finds an element of projective order 5; alpha checked as order 5).
ORBIT 3 4 4 is worse than 3 5 1 on the current group. PSL shapes are worse at k = 3 (involution holes), as in ODD_D_HOLES.md.
n = 169 (current) stays best among SL shapes in median; k = 5 is not better per unit mu.
- SL(2,139) x Z65, ORBIT 3 5 1, 85 s, K = 4 (seed 34): best 26 after 21 evaluations (5 steps); best state sl139_65_k3.txt.best.
  Lowest anneal cost of the three pairs tried (ref 32, PSL(2,109) x Z271 k5 31).
- Resume of that state (START=sl139_65_k3.txt.best, seed 35, 85 s): no gain, best stays 26 after 21 evaluations (cost 32 at the current S; the search rarely returns to best). Not solved.
