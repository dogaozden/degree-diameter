# c10: q-dependent Delta = 7 (1+3+3) families, PSL(2,q), m = 1

Generator: gen_c10.py q m variant (16 variants, see docstring). Screens: screen_v*.json (q = 29,41,53,61).
Full scores (q in [23,113], 22 primes): full_v{1,5,12,13,14}.json. Conditional variants (need a root or a
congruence): cond_v{7,8,9,10,11}.json on their applicable primes only. Random baseline: random_s{1,2,3}.json
(gen_random_orb.py q 1 2 SEED).

Results (mean_excess, lower is better):
- v12 X=[[g,1],[0,g^-1]], Y=[[1/2,g],[g,2(1+g^2)]]: 2.963 (22 q, all connected). Best of the 16 variants.
- v13 X=[[g,1],[0,g^-1]], Y=[[g,0],[1,g^-1]]: 3.008. v14 (X exponent g^2): 3.008.
- v1 (card example) and v5 (Y = [[2,1],[1,1]]): 3.054.
- Random Delta = 7 (3 seeds, same 22 primes): 3.054, 3.236, 3.054 (average 3.114).
- Conditional, on their own primes vs random average on the same primes:
  v7 (zeta, q=1 mod 3) 3.108 vs 3.075; v8 (i) 3.452 vs 3.027; v9 (i) 3.361 vs 3.027;
  v10 (sqrt 2) 3.010 vs 3.040; v11 (sqrt 3) 3.068 vs 3.189.
- Degenerate or bad: v4 (unipotent pair) 5.54, v6 (integer matrices) 4.54, v15 (torus + unipotent) 4.04,
  v16 (SL2(Z) standard generators) 12.5.

Caveat: 16 variants were tried and the best was picked on 4 primes, so the 0.15 gain over the random mean
is at most a weak signal. Per-q, v12 beats random seed 1 on only 2 of 22 primes. Excesses mostly take the
same values across variants because diam is an integer and only the diameter at each q changes the score.
