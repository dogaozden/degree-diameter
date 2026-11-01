# w06 FAMILIES: odd-order Frobenius and near-Frobenius groups at (6,9)

Screen: `haar_gen3 6 9 1 1 8 /dev/null <GROUP> 1` with `RANDSAMPLE=1000 THREADS=1` (random S, no search; seed 1).
Columns: min and median of the uncovered count over 1000 random S (the lower the better), p1 = 1st percentile.
mu = N exp(-W/N), W(6,9) = 488,281. Bar: N >= 63,649 for a record (2N > 127,296).

| group | N | mu | min | p1 | median | note |
|---|---:|---:|---:|---:|---:|---|
| SL(2,17) x Z13 (control, current value family) | 63648 | 29.7 | 26 | 46 | 138 | plain random S, 1000 samples |
| Z2551 x| Z25, r=7 (Frobenius) | 63775 | 30.2 | 22 | 28 | 74 | a03 2000-sample run: min 16, median 72 |
| Z1559 x| Z41, r=84 (Frobenius) | 63919 | 30.8 | 16 | 28 | 68 | best median at N < 64k |
| Z4261 x| Z15, r=290 (Frobenius) | 63915 | 30.7 | 42 | 60 | 184 |  |
| Z2377 x| Z27, r=7 (Frobenius) | 64179 | 31.9 | 18 | 34 | 106 |  |
| Z3067 x| Z21, r=292 (Frobenius) | 64407 | 32.8 | 32 | 46 | 130 |  |
| Z4967 x| Z13, r=307 (Frobenius) | 64571 | 33.6 | 30 | 40 | 126 |  |
| Z4993 x| Z13, r=492 (Frobenius) | 64909 | 35.1 | 22 | 44 | 128 |  |
| Z3109 x| Z21, r=85 (Frobenius) | 65289 | 36.9 | 26 | 50 | 144 |  |
| Z1777 x| Z37, r=4 (Frobenius) | 65749 | 39.1 | 24 | 38 | 86 | k=37 is the best k above 41 in the window |
| Z3877 x| Z17, r=403 (Frobenius) | 65909 | 39.9 | 34 | 44 | 120 |  |
| Z3911 x| Z17, r=29 (Frobenius) | 66487 | 43.0 | 36 | 46 | 126 |  |
| Z5897 x| Z11, r=227 (Frobenius) | 64867 | 34.9 | 24 | 44 | 164 | k=11 prime |
| Z5963 x| Z11, composite m, r=64 (Frobenius) | 65593 | 38.4 | 24 | 54 | 186 | composite m, fixed-point-free |
| Z5963 x| Z11, composite m, r=223 (Frobenius) | 65593 | 38.4 | 42 | 56 | 182 |  |
| Z3 x| ... k=9 Frobenius (Z7129, Z7219, Z7237 x| Z9) | 64.9k-65.1k | - | 144 | 190 | 650 | k=9 is 5-10x worse than k >= 11 in median |
| Z2551 x| Z25, r=468 (ord 5, centre Z5) | 63775 | 30.2 | 220 | 334 | 1236 | non-Frobenius: central holes |
| Z1831 x| Z35, r=123 (ord 5, centre) | 64085 | 31.5 | 248 | 364 | 1360 | non-Frobenius |
| Z1423 x| Z45, r=289 (ord 9, centre Z5) | 64035 | 31.2 | 40 | 68 | 322 | non-Frobenius |
| (Z7 x| Z3) x (Z79 x| Z39) (odd product) | 64701 | 34.2 | 18 | 36 | 150 | product of two odd Frobenius |
| (Z7 x| Z3) x (Z1021 x| Z3) (odd product) | 64323 | 32.5 | 1470 | 1818 | 7594 | degenerate (two order-3 factors) |

Orbit/annealing results (haar_gen3s, plain S, no orbit: ORBIT is degenerate on Frobenius groups, see FROBENIUS.md):
- Z1559 x| Z41 r=84, seed 11, 90 s: cost 12 -> 8 (best 8, 43,338 evals); resumed seed 12 90 s: stays 8;
  haar_gen3t TFULL=1 TARGP=100 90 s from the cost-8 state: no move accepted (0/1055 plain). Saved best_1559_41_s12.txt.
  (a03 round 1 reached cost 6 on this group.)

Reading: Frobenius groups Z_p x| Z_k with k in 25..41 and N ~ 63.8k-64.0k are the best medians (68-74 vs 138 for
the current SL(2,17) x Z13). Smaller k (9, 11) and composite m with k = 9 are much worse; non-Frobenius groups (any
centre) are 4-10x worse (the central-element holes of the odd-D theory); products of two odd Frobenius groups are
worse than either factor's direct analogue, and the product with two order-3 factors is degenerate.
No family in the window beats the current value by annealing so far: the best state is cost 6 (a03) / cost 8 (w06).

Later runs on Z1559 x| Z41 (r=84), haar_gen3s, 95 s each: seed 21 fresh -> cost 10; seed 31 chained from the
seed-12 state -> cost 8. Best states: best_1559_41_s12.txt, best_1559_41_s31.txt. No cost-0 state, no solution file.
