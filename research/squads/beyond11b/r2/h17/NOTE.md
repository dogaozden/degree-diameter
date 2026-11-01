# h17 NOTE: words in Frobenius groups Z_p x|_r Z_k at odd D (theory + checks)

Setting: G = Z_p x| Z_k, (a,j)(b,l) = (a + r^j b, j+l), r of order k mod p. H(G,S), D = 2h+1, same-side ball
X_A = (S^-1 S)^h, X_B = (S S^-1)^h. Code: frob.py (exact BFS, non-backtracking counts), analyse.py, ens.py, ens2.py,
labels_enum.py, label_rule.py, cmp_k.py. Checks: build_haar2 VALID for the (4,11) reference and the new (5,11) graph.

## 1. No involutions, trivial centre (proof)
|G| = pk is odd, so G has no involutions. Centre: a central c must commute with N = Z_p; (a,j) with a != 0
centralises N only if r^j = 1, so j = 0; c = (b,0) commutes with (0,1) only if r b = b, so b = 0. Hence Z(G) = 1.
Brute-force check on Z_61 x| Z_5, Z_19 x| Z_3, Z_37 x| Z_9: 0 involutions, centre size 1.
So the reversal clump (lemma item 1) and the rotation clump (item 2) of ODD_D_HOLES.md never apply.

## 2. Clumps of single elements
Inversion gives an exact bijection between words for x and words for x^-1, and x != x^-1 for every x != e. That pairs
different elements, so it creates no clump on one element. Conjugation does not preserve S, so no other symmetry
exists for a random S. Measured at (4,11), sol_m761_k19_r25_s2 (non-backtracking counts, 10 steps, 78,732 walks):
mean 5.36 on the kernel j=0 (var 4.90), mean 5.45 off the kernel (var 4.64). No clump is visible.

## 3. Coset coordinate (exact)
Lazy words (all s_i in S, e in S): coset distribution f(z) = (sum_s z^{c_s})^h (sum_s z^{-c_s})^h, c_s = label of s.
Fourier: f^(t) = |phi_t|^{2h}, phi_t = sum_s w^{t c_s}, w = e^{2 pi i/k}. f_j = f_{-j} (inversion symmetry).
Non-backtracking coset counts W_j come out equal to the label-only DP (max diff 0). Verified on the 761/19 sol:
W_j symmetric under j -> -j; W_j in [4080, 4195]. Lazy sums in [54606, 56914] (sum = 4^10).
Reachability: lazy support = h-fold sumset of D = {c_y - c_x : x,y in S}. For prime k, Cauchy-Davenport gives full
coverage when |D| >= (k-1)/h + 1. Exhaustive check at (4,11), k = 19, h = 5 (all 1330 label multisets with label(e) = 0):
every multiset with >= 3 distinct labels reaches all 19 cosets (459 + 816 = 1275, lazy and NB agree); the 55 with <= 2
distinct labels fail. Rule: S needs >= 3 distinct labels.

## 4. Size-law variant for G
Holes per side are about sum_j p exp(-W_j/p) >= N exp(-W/N) (Jensen), W = Delta (Delta-1)^(2h-1), N = pk.
For the reference, the coset law gives 62.5 vs the size law 62.4, so the penalty is tiny. For random S (>= 3 labels,
200 samples, (4,11)) the coset-level prediction is still a good log-scale predictor (log-corr 0.70), but the actual
median is 36 holes against 62 predicted. The coset imbalance is driven by max_t |phi_t|/Delta: correlation of log holes
with log(max W_j ratio) 0.66, with max_t |phi_t|/Delta 0.54. Lifts of label multisets ranked by max_t |phi_t|/Delta
(70 trials each, (4,11)): best 10 sets median 25 holes; middle 28; worst 10 sets median 145. The reference label set
{0,1,7,11} is the most balanced one (max |phi|/Delta = 0.575).

## 5. The number of cosets k matters a lot (main finding)
(5,11), Delta = 5, random S with >= 3 labels, median holes per side (size law N exp(-W/N) in brackets):
- Z_21589 x| Z_7 (N = 151,123, r = 17486): median 434 (26), min 128 (53 samples).
- Z_7829 x| Z_19 (N = 148,751, r = 2039): median 35 (22), min 4 (44 samples).
So the Frobenius law is bad with small k: the word coordinate is a sum of +-r^t a_s with t in Z_k, and with k = 7
there are only 7 such coefficients (hypothesis for the reason; not proven).

## 6. New construction: Z_8171 x| Z_19 at (5,11) (N = 155,249, r = 8108)
Annealing with haar_gen3 (meta 8171 19 8108, d = 5, D = 11): seeds 1-5 stopped at cost 8, 8, 2, 10, 8 (90/90/90/44/44 s).
Seed 6 reached cost 0 after 27 s. build_haar2: VALID d=5 D=11, 310,498 vertices, 776,245 edges.
This beats (5,11) = 301,200 by 3.1 %. Solution: sol_m8171_k19_r8108_s6.sol (edges_m8171_k19_r8108_s6.txt).
Not yet independently checked by apsp (too slow at this size); the director should rerun build_haar2 if needed.

## 7. Larger attempts (not solved)
Z_8513 x| Z_19 (N = 161,747, r = 2673), d = 5, D = 11: seed 6 best 14, seed 7 best 18 (88 s each). Larger p is harder
at this budget; the 155,249 group needed a lucky seed (27 s at seed 6, cost 2-10 at other seeds).
