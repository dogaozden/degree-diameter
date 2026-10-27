# c2: integer lifts, Delta = 7, type 1+3+3 (psl)

Generator: gen_c2.py q m F X Y (F in I,w,w2; X,Y integer det-1 matrices; S = {F} u O(X) u O(Y) over Z, reduced mod q).
Screen: screen_c2.py --qs 29,41,53 -> screen.tsv (all 32 integer orbits with entries in [-3,3], all unordered pairs, 3 F: 1212 valid sets).
Top screen scores tie at 2.886 (q=29,41,53). Full scores (q in [23,113], psl, 22 primes) of the first 10 rows: run_full.sh, full_1..10.log.

Full mean_excess: best 3.099 (F=I, X=-3,-2,2,1, Y=0,-1,1,3); the other nine 3.099-3.599 (mean 3.354).
Random Delta=7 baseline (gen_random_orb.py q 1 2 SEED): 3.054, 3.236, 3.054, 2.963, 3.054; mean 3.072, sample sd 0.10.
Conclusion: bounded-height type 1+3+3 families are no better than one random draw on average (3.35 vs 3.07), and the best one ties a typical draw.
