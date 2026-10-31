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

## 8. Why the abelian lifts stall (argument, 18:50)
For a lift by an abelian group, a walk of length <= 4 from (s,0) to a same-side base vertex u gets its voltage as a sum of
<= 4 signed voltages, and commutativity makes many of the ~750 walks give the same sum. With a 7+7 base, each target u
needs all 49 voltages covered by about 107 walk sums; random sums miss about e^(-107/49) = 11% of the residues, so
the cost floor sits near 7 x 49 x 0.11 = 38 per source, and the SA plateaus at 64-90 (observed: 64, 66, 82, 86, 86).
Groups of order 49 are all abelian, so the (7,49) lift family is commutativity-limited. At 686 the only
non-abelian group of order 343 is the Haar case (closed), so no lift with a non-abelian group exists at exactly 686
except bi-cosets with stabilizers (sections 2, 3, 5: best costs 30, 304, 56). The round-1 2+2 lift by C11:Q16 (cost 4) is
the non-abelian case that works best, which fits this picture.
S3 stabilizer (|G| = 2058): mk_h.g found no S3 action by random sampling. Built by hand instead (mk_s3aff.g):
G = F_7^3 x| S3, S3 = <diag(1,2,4), swap of coordinates 2,3> as affine permutations on 343 points. Exhaustive dcenum
(x2058/S3aff_1_1.dc2, 2373 unions): best cost 414 (bad 71001 by check.sh on that cost-414 graph). Poor.
Tabu (shared/tabu) needs a gauge-normalised input: gauge_cyc.py (cyclic groups). Tabu from the cost-64 lift: no gain in 200 s.

## 9. Final runs (18:50-18:56)
More 7+7 Z49 bases: seed 21 (simple, SWAP 0.05, 230 s): cost 86, bad 2107. Multi-edge base seed 31 (SWAP 0.05, 230 s):
cost 78, bad 1911. The floor over 7 bases is cost 64-90 (bad 1568-2254). No cost-0 lift found in this family.
Processes: none of this worker's left running at 18:56.

## Next ideas (not done)
- S3 stabilizer at |G| = 2058 with a hand-built action (inverting automorphism) and the same exhaustive dcenum.
- Bi-coset stabilizer 3 on the other nonabelian groups of order 1029 (more automorphism classes than the 10 sampled).
- A non-abelian base for the lift family at 686 does not exist (only Haar), so new 686 searches should be bi-cosets with
  non-abelian G (done for 3, 4, 6 with poor costs) or non-symmetric surgery from the 684 Haar graph (c7/c13).
