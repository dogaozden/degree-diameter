# c16 (wildcard) notes

Plan: a family nobody in round 1/2 tried: Lazebnik-Ustimenko D(3,q) graphs.
D(3,q) is q-regular bipartite on 2 q^3 vertices with girth 8. For q = 7 that is 686 vertices, exactly the
target size. Degree 7 is one too many, so the candidate is D(3,7) minus a 1-factor (6-regular, 686 vertices).
Also: 1-factors invariant under a group (affine maps) give a small search space.

Calibration plan: check D(3,5) (250 vertices) diameter first, then D(3,7).

## 1. Lazebnik-Ustimenko D(3,q) (q=7, 686 vertices): DEAD
gen_ld.py q OUT: points (p1,p2,p3), lines [l1,l2,l3], incidence l2+p2 = p1 l1, l3+p3 = p1 l2 (mod q).
D(3,7) is 7-regular, bipartite, girth 8, diameter 6 (bad=0 at D=6, bad=3087 at D=5). Every subgraph has bad >= 3087
at D=5 (deleting edges cannot shorten paths), so a 1-factor removal is hopeless. D(3,5): bad 750 at 250 vertices.

## 2. Bi-coset B(G;H,K), |H|=|K|=3, |G|=1029 (686 vertices): not in round 1/2 (c4 swept 3|3 only at 1083..1149)
SmallGroups library has no order 1029 (NrSmallGroups errors). Built G = P x| C3 by hand (P = SmallGroup(343,i), Sylow 7
normal), automorphisms of order 3 sampled up to conjugacy (mk1029.g, 26 pairs of order-3 subgroup classes).
dc2_lib.g ExportPairs + shared dcenum (exhaustive, DELTA=6, D=5). Results: x1029/res_d5.txt.
Best exhaustive cost (vertices missed by two roots) 30 (G = C49 x| C3 family), which is bad=5145 pairs in check.sh.
Unions with cap hit (2e6): pairs 2_2, 2_4, 5_3, 5_4 (best 248-250 in the capped search). Verdict: far from 686.
Calibration at D=6: exhaustive finds no cost-0 for the first pair either (best 6), so this family is weak in general.

## 3. Stabilizer-4 bi-coset (|G| = 1372 = 4 x 343, n = 686): poor
mk_h.g (QN=C4): P x| C4 with C4 acting through automorphisms of P (C49 x C7 and C7^2:C7 and C7^3 have order-4
actions only for some P; 8 groups). Exhaustive dcenum DELTA 6 D 5 (x1372/res_d5.txt): best cost 304 (groups with
C7^2 : C4) and 584. Stabilizer-3 (|G| = 1029) gave cost 30 (bad 5145). Trend: the larger the stabilizer, the worse.
Stabilizer 2 is the best bi-coset class (cost 8 at 686-720, round 1). V4 sampling was too slow (GAP Normalizer/
Centralizer in Aut(C7^3) = GL(3,7)): one group only, not scored.

## 4. Lifts with b = 7 (7+7 base) and m = 49 (the only lifts of order 686 besides Haar)
grp_tab.py (cyclic and Z7xZ7 tables), mkbase_z7.py (random 6-regular base, voltages in Z_m), vl SA 60 s each:
  Z49, base seeds 2,3: vl cost 86 and 92 -> check.sh bad 2107 and 2254 (export_lift.py).
  Z7 on a 49+49 base (294 edges, 150 s): vl cost 1042 (random-like). Large base + small group = poor, as expected.
Round 1 c2 (kminus base, p=7 m=49..51): best cost 90. Same regime, same answer.

## 5. Stabilizer-6 bi-coset (|G| = 2058 = 6 x 343, n = 686): poor
mk_h.g QN=C6 (C6 and S3 actions, 18 pairs). Exhaustive dcenum (x2058/res_d5.txt, tiny unions ~60 each): best cost 56
(C6_g3_1), bad 9604 by check.sh. S3 stabilizers not run (time).

## 6. Haar + free matching (hfree.c): DEAD for random S
K Haar matchings from Z_7^3 plus one free permutation sigma, 2-switch SA on sigma with exact bitset ball growth
(12k cost evaluations/s). Start bad ~12000-20000 (5-regular part is far from Moore-tight: bipartite Moore for degree 5,
diameter 5 is 682 < 686, so five matchings cannot reach diameter 5 at 686). Random Haar-6 on Z_7^3 (haarmin.c, 20000
random 6-sets): best bad 37044 (abelian Haar sets are very collision-heavy). Not a useful start.
(HAAR6=1 variant, sigma started as the 6th Haar matching): no progress in 150 s.

## 7. Lifts b=7, m=49 (7+7 base), longer runs
  Z49, base seed 5, SWAP 0.05, 240 s: cost 64 -> bad 1568 (b7_s5_z49.edges, the best of this round; scoreboard line added).
  Continuation of that run (240 s more): no change (64).
  Z7xZ7, same base, 240 s: cost 66 -> bad 1617.
  Z49, base seed 11, SWAP 0.1, 240 s: cost 82 -> bad 2009.
  Z7 on 49+49 base (294 edges), 240 s: cost 866 (very slow SA, 72k steps).

## Verdict (c16, 17:45-18:45)
No graph above 684. Families and best numbers (bad = pairs at distance > 5, check.sh):
  D(3,7) Lazebnik-Ustimenko: deg 7, diam 6, bad 3087 at D=5 (every subgraph is worse): closed.
  bi-coset |H|=|K|=3, |G|=1029: best bad 5145 (exhaustive). |H|=4 (|G|=1372): best cost 304. |H|=6: bad 9604.
  lifts 7+7 by Z49 or Z7^2: best bad 1568. lifts 49+49 by Z7: cost ~900+ (bad large).
  Haar + free matching: thousands.
Compared with the squad's best at 686 (c7, 177), none of the new families is close. The bi-coset stabilizer-2 class
(best cost 8) and the 2+2 lifts (cost 4) remain the structured near misses; the 686 Haar family is closed.
Ideas not tried: exhaustive bi-coset with H != K at stabilizer 3 on the other 1029-groups (SmallGroup library lacks
1029; only 26 pairs from 10 sampled order-3 automorphism classes were built), S3 stabilizers of order 6, and vl
with the Z49 lifts restarted from many random bases (cost 64-90 each).
