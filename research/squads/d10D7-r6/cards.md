# Round 6 cards
- c1 MANY T_3 CORES: build new 31-34-orbit cores with mis_csr on T3_conf.bin using other seeds and longer runs.
  Run pov2 from each core for 150-300 s and keep the best final set. Report the core sizes against the final sizes.
- c2 (revised by Opus after the S7 finding below) GROUPS OUTSIDE Sp(6,2): orbit unions for subgroups of Sp(6,8) that
  do not fix a W(5,2) subgeometry, then pov2 from the best union. Candidates: Sp(2,8) wr S3 (block-diagonal
  diag(A1,A2,A3) on the hyperbolic pairs (x0,x3), (x1,x4), (x2,x5) and permutations of the pairs) and its subgroups;
  SL(3,8) and SU(3,8) as diag(A, A^-T); the field-reduction groups (torus T of order 513 with the Frobenius, SL(2,512)
  elements in the L-model of r5/c4); PSL(2,13), A7 or other small groups if you can realise them. Tools:
  research/d10D7/ovoid/subgeo.py (orbits(), orbit_graph(), max_weight_clique()) and orbsearch.py as an example.
- c3 BIG KICKS FROM 217: iterated local search with large perturbations. Remove 10/25/50 % of the 217 set, either at
  random or as a "region" (the points near a random point or near a random hyperbolic line). Regrow with pov2. Also
  try crossover with other sets (half of 217 + half of the 134 set or a fresh core).
- c4 H(9) NON-COLLINEAR: push 4,277. Try a longer quotient tabu for 48+ orbits of 91. Following the q = 8 lesson, run
  an unrestricted tabu (r4/c4 mis.c with INIT) from the orbit set. Also try orbit cores of other elements (order 7, 13,
  73, 91, Frobenius-twisted).
- c5 q = 7 AND q = 5: the same structured-start trick for H(7) (288; research/d10D7/sets/P7_c5_288.txt, (9,7) record
  118,224) and H(5) (72; sets/P5_c6_72.txt, (7,7) record 23,580). Use orbit cores of hexagon automorphisms, for example
  diag(A, A^-T, 1)-type elements as in r4/c3 (orbit7.py), then an unrestricted tabu (r4/c5 mis_tabu.c).

FINDING (Opus, 00:20 UTC): the 217 set found independently by r5/c4 and r5/c3 is the same object. It is a union of two
orbits of S7 x C3 ≤ Sp(6,2) x Gal(GF(8)/GF(2)): the 7 GF(2)-points of a maximal partial ovoid of a W(5,2) subgeometry
(Gram matrix J - I) plus one orbit of 210 points. Its full stabiliser is S7 x C3. The exact maximum union of orbits is
again 217 for S7, A7, S6, L3(2), 7:6, 7:3, S5xS2 and S4xS3, each with or without the Frobenius
(research/d10D7/ovoid/orbsearch.py). r6/c3: every kick from 217 regrows the same set.
- c6 H(9) BY SUBGROUP ORBITS: the same exact orbit-union search for non-collinear sets of H(9) under subgroups of
  SL(3,9) acting as (v, a, w) -> (gv, a, g^-T w) (r5/c6 grp.py has this action). Candidates: SU(3,3) (order 6048),
  SL(3,3), Omega(3,9) = A6, L2(7), the Singer normaliser 91:3, each with or without the Frobenius x -> x^3. Then run
  an unrestricted tabu (r4/c4 mis.c with INIT) from the best union. Score with setcheck "points noncollinear".
