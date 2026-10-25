# Round 6 cards
- c1 MANY T_3 CORES: build new 31-34-orbit cores with mis_csr on T3_conf.bin using other seeds and longer runs.
  Run pov2 from each core for 150-300 s and keep the best final set. Report the core sizes against the final sizes.
- c2 OTHER GROUPS AS CORES: cores from T_9, T_19, T_27, T_57 and the 7 L73 cores, plus groups with the Frobenius
  (TF in run_orb.py, or your own). Run pov2 from each. Which group gives the best basin?
- c3 BIG KICKS FROM 217: iterated local search with large perturbations. Remove 10/25/50 % of the 217 set, either at
  random or as a "region" (the points near a random point or near a random hyperbolic line). Regrow with pov2. Also
  try crossover with other sets (half of 217 + half of the 134 set or a fresh core).
- c4 H(9) NON-COLLINEAR: push 4,277. Try a longer quotient tabu for 48+ orbits of 91. Following the q = 8 lesson, run
  an unrestricted tabu (r4/c4 mis.c with INIT) from the orbit set. Also try orbit cores of other elements (order 7, 13,
  73, 91, Frobenius-twisted).
- c5 q = 7 AND q = 5: the same structured-start trick for H(7) (288; research/d10D7/sets/P7_c5_288.txt, (9,7) record
  118,224) and H(5) (72; sets/P5_c6_72.txt, (7,7) record 23,580). Use orbit cores of hexagon automorphisms, for example
  diag(A, A^-T, 1)-type elements as in r4/c3 (orbit7.py), then an unrestricted tabu (r4/c5 mis_tabu.c).
