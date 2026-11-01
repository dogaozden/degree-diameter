# w17 NOTES: mixed-orbit graphs (G regular on side A, B = union of orbits G/H_i)

Start: 2026-11-01 00:53 UTC. Deadline: about 02:55 UTC (2 hours). Last update: 00:55 UTC.

## Plan
- Family: G of order N, n = 2N. B = disjoint union of coset spaces G/H_i. Edge orbit j attaches A to B-orbit i(j)
  through a coset s_j H_i. Degree 4 everywhere needs sum_i 1/|H_i| = 1 (types (1), (2,2), (2,4,4), (4,4,4,4)).
  Four edge orbits in total; orbit i gets 4/|H_i| of them.
- WLOG the first edge orbit uses the identity coset (left-multiplying all s_j by s_0^{-1} gives an isomorphic graph).
- Cost = unordered far pairs (distance > D) from the orbit roots, weighted by orbit sizes.
- Code: mix.c (evaluator + annealing), mkcfg.py (subgroups of order 2 and 4, conjugacy classes, config files).
