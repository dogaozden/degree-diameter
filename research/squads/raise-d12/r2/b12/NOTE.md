# b12 NOTE (written before coding, start 23:28 UTC)

Idea: inverse-closed (symmetric) connection sets S = S^{-1} in Haar graphs H(G,S).
H(G,S) with S = S^{-1} is the bipartite double cover of the Cayley graph Cay(G,S).
No card in round 1 or 2 (per the card list) restricts S this way; all Haar searches so far sample S freely
(random, or orbit-closed under an automorphism alpha).

Hypothesis: for S = S^{-1}, the left-inversion h -> h^{-1} maps distances in Cay(G,S) to themselves
(d(e,h^{-1}) = d(e,h) since S is symmetric), so the uncovered B-elements should come in pairs {h, h^{-1}}
(fixed points: the involutions and e). Then P(cost 0) ~ exp(-mu/2) instead of exp(-mu), a gain like the
orbit-closed k = 2 case but without the even-k word coincidences that hurt alpha-orbits (the inversion is an
anti-automorphism, so the coincidence argument may not apply). Degrees of freedom are fewer: for Delta = 4,
S = {a, a^-1, b, b^-1} (2 params) or {a, a^-1, t1, t2} with involutions t1, t2.

Test plan:
1. Group: Z731 x|_7 Z48 (the (4,12) record group, N = 35,088, 2N = 70,176), the random-S control on the same group.
2. Measure the cost distribution (cost = # B-elements at distance > 11 from (e,A)) for random S and for
   random symmetric S; check the pairing h <-> h^{-1} of uncovered elements directly.
3. If pairing holds: annealing over symmetric S (swap one pair or involution), chain runs, then verify any
   cost-0 S by a full independent BFS (eccentricity of (e,A) and (e,B), which gives the diameter since the
   right regular action is transitive on each side).

Scorer: BFS-based cost in C (bfs.c here) plus independent Python verifier.

## Results (23:28-23:40 UTC)
- Tool: hsym.c (BFS cost, depth-limited; verified equal to an independent Python BFS on one S: cost 56 both).
- Pairing hypothesis CONFIRMED for symmetric S: uncovered B-elements pair exactly under h -> h^{-1} (100 %, self-inverse
  involutions only 0.05 %). Random S: only 71-73 % of holes are paired (no structure).
- But the effect does not pay: the symmetric family is much less likely to hit cost 0.
  Z241 x|_178 Z48 (N=11,568): symmetric 268/1434 cost-0 (18.7 %); random 540/880 (61 %).
  Z337 x|_199 Z48 (N=16,176): symmetric 77/915 (8.4 %); random 306/605 (50.6 %).
  Z433 x|_295 Z48 (N=20,784): symmetric 18/640 (2.8 %); random 111/489 (22.7 %).
  Z731 x|_7 Z48 (N=35,088, record group): symmetric 1,450 samples, best cost 52, mean 20,067 (0 of 1,450);
  random 549 samples, best cost 6, 0 zero-cost (no hit at this size in this budget).
- Q = 2 or 4 involutions (Z337 x| Z48, all 337 (x,24) are involutions in one coset): products of two involutions
  lie in Z_m, so the generated subgroup is tiny: best cost 10,045 (Q=2), 15,839 (Q=4).
- Valid by full independent BFS (verify_full.py, diameter <= 12, regular): sol_m241_..., sol_m337_..., sol_m433_...
  (random-S solutions: the files were overwritten by the later random runs; file name's "D4" is the Delta, not D).
  These give 2N = 23,136 / 32,352 / 41,568 vertices, below every (4,12) value to beat (70,176).
- Verdict: negative. Inverse-closed S is a strict subfamily; holes do cluster in inversion pairs, but the lost freedom
  costs more than the pairing gains (about a factor 3-8 in success rate at N = 11k-21k).
- Random S on the record group Z731 x|_7 Z48 (90 s, 1,564 samples): best cost 4, 0 zero-cost (random sampling alone
  does not reach 0 at N = 35,088; consistent with the record needing search).
- Symmetric annealing (mode 2: replace one inverse pair per move, SA acceptance, 2,322 + 1,054 steps): stuck at cost 52
  (26 holes-pairs). Holes sit in a few Z_48 classes (y-histogram: nonzero only near y = 0, 1, 10-14, 23-25, 34-37, 47),
  while the state's letters have y = +-18, +-19 only. The Z_48 abelian image of words of length <= 11 with letters +-c1, +-c2
  is the wall (the abelian-quotient wall of HEADER round 1), and inverse-closed S makes it tighter than free S does.
- Final: negative for (3,12) and (4,12). No raise. Valid graphs found only up to 2N = 41,568.
