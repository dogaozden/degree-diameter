# c1: integer lifts, Delta = 6, type 3+3 (S = O(X) u O(Y), PSL)

Files: gen_lift.py (generator: q m x1..x4 y1..y4), screen.py (all pairs, symmetry-reduced), screen.tsv (206 surviving pairs,
scored on q = 29, 41, 53), top10.tsv, run_top10.sh, logs/full_<rank>.txt (family_score on q in [23,113], 22 primes).

Symmetry reduction: 116 det-1 integer matrices in the box [-3,3]^4 fall into 32 classes (orbit under conjugation by w, sign).
Pairs of classes reduced by conjugation by the 12 elements of GL(2,Z) with entries in [-2,2] normalising <w>; pairs with a
coincidence mod any prime in [23,113] dropped (210 canonical pairs, 206 screened ok; the rest disconnected or non-distinct).

Results (mean_excess over 22 primes q in [23,113]; height = max |entry| of X, Y at the minimal representative):
- best full score 3.358 (X = [[-2,-1],[1,0]], Y = [[-1,-2],[1,1]], height 2; also X = [[-2,-1],[1,0]], Y = [[-1,-1],[2,1]])
- best full score at height 3: 3.358 (X = [[-3,-2],[-1,-1]], Y = [[-3,-1],[-2,-1]]); the screen's best (2.898) fell to 3.404.
- top-10 full scores range 3.358-3.586. Random alpha-closed draws give 3.2-3.5, LPS p=5 gives 4.00.
- screen (3 primes) by height: height 1 best 5.23 (mean 9.07, n = 6); height 2 best 3.23 (mean 4.62, n = 33);
  height 3 best 2.90 (mean 4.09, n = 167). Height-1 sets are far worse; heights 2 and 3 are indistinguishable at the top.
- the 3-prime screen is noisy: screen means of 2.9-3.2 became 3.36-3.6 on 22 primes.
- D = 8 is not reached by any top-10 family (min diameter 9 at the best q); D = 9 gives 0.254 and D = 10 gives 0.665 of the table.
