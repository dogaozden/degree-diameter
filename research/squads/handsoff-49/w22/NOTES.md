# w22 NOTES (wildcard: a family nobody in the squad has tried)

Start: 2026-11-01 01:23 UTC. End: 02:55 UTC. Commands kept under 110 s per the coordinator's rule (chained short runs).

## Key analysis (why random-like families fail)
- Bipartite, 4-regular, n = 2N. Same-side pairs need EVEN walks of length <= 8 (distance <= 9 and same side means even).
  Non-backtracking even walks from a vertex of length <= 8: 12 + 108 + 972 + 8748 = 9840, for N = 2486 targets per side,
  so the mean multiplicity is about 3.96 per target.
- A random 4-regular bipartite graph therefore misses about e^-3.96 of each side: measured with randbip.py at n = 4970,
  score48 gives far = 119,635 pairs. Any construction must make the even-walk coverage (almost) exact. Only group
  algebra (Haar graphs) does that: the valid 4,970 graph has zero far pairs.
- Abelian groups cannot work at all: even words collapse to at most 1,742 values < 2,486 targets.

## Families tried
1. Compound of K = 7 copies of the H(3) incidence graph (728 vertices, girth 12, diameter 6; checked with apsp at D=6),
   each copy minus a random perfect matching (inner graph 3-regular), the 4th edge being a cross edge in a random
   bijection between points and lines of all copies. n = 5,096. Not a covering, so w4's girth/fibre argument does not
   apply, but the walk count does: random-like. Initial far = 149,221 (= random baseline). Annealed 460 s: 81,619
   (scoreboard line). Still ~80,000 pairs away from zero. Dead.
   Code: comp.c (annealer over the cross matching), gen_base.py, bfsprof.py.
2. Mixed bi-Cayley graphs (left AND right translations): (g,A) ~ (s g,B) for s in S and (g,A) ~ (g t,B) for t in T,
   |S| + |T| = 4. This contains the Haar family (T empty) and is not isomorphic to it in general (inversion only swaps
   left and right). Code: mixed.c (also runs pure Haar with |S|=4).
   Results (same annealer, same schedule T 30 -> 1):
   - pure Haar |S|=4, meta 71 35 49 (n=4970): cost 0 in 33 s (valid, calibration row)
   - mixed |S|=1, meta 71 35 49, 240 s: far 34,195 (not 0)
   - mixed |S|=2, meta 71 35 49, 120 s: far 350,485 (worse than random)
   - mixed |S|=1, meta 104 24 7 (n=4992), 300 s: far 25,776
   Conclusion: mixing left and right translations destroys the group coverage. Dead as a Haar substitute.
3. Semidirect Z_p^2 x| Z_k (p=17,k=9 order 2601; p=7,k=51 and k=52): pure annealer gives far 36,414 (p=17) and
   millions for p=7 (large centre, abelian-like, disconnected). Dead for the usual reason (big abelian normal subgroup).


4. Centreless or small-centre screens with the pure-Haar annealer (|S|=4, 60-85 s each, T 30 -> 1):
   - AGL(1,7) x Z_61 (N=2562, centre 61): far 2,185,386. AGL(1,11) x Z_23 (N=2530, centre 23): far 488,290.
   - A_5 x Z_43 (N=2580, centre 43): far 54,180.
   Large cyclic centres are very bad here (the central part of the even words is almost abelian). Not records.

5. Frobenius-type semidirect groups with a small complement (haar_tab 45-60 s screens): Z_29^2 x| Z_3 (N=2523, Frobenius)
   best 2296; Z_11^2 x| Z_24 (N=2904, Singer-type order 24) best 438; Z_17^2 x| Z_9 (N=2601, Frobenius) best 28 (agrees
   with the squad table). The index of the abelian normal subgroup is the problem: index 3 or 24 gives poor even coverage.

6. Sanity check of the annealer: pure Haar on meta 104 24 7 (N=2496, proven minimum cost 4): best 4,992 far pairs
   in 85 s, never 0. Consistent with the exhaustive minimum, so no false zeros.

## Best result of w22
- No record. Best valid n is the calibration graph n = 4,970 (not above 4,970). Best near-miss at n > 4,970: compound
  n = 5,096, 81,619 far pairs (random-like). Mixed n = 4,992: 25,776 far pairs.

## What I would try next
- The even-walk coverage bound says the only route is exact covers in a group of order 2486..2600 with few short
  relations. The mixed family does not help. I would use a fast Haar annealer on groups with trivial centre and no
  large abelian normal subgroup, screened by even-walk coverage alone (cheap, no full BFS).
