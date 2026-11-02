# g15: bi-coset graphs with non-trivial stabilizer (wildcard, Delta 3..6 at D = 10)

Family (not Haar, not lifts): G = Z_m x|_r Z_k, H = <(0, d)> of order h = k/d, NON-normal (r^d != 1 mod m).
Vertices = G/H (left cosets) on each side, xH ~ yH iff x^{-1}y in T, T a union of double cosets HtH with |T| = Delta*h.
Biregular of degree Delta, G acts transitively on each side, so cost = far(A-rep) + far(B-rep) is exact (0 iff diam <= D).
Code: bicoset.c (simulated annealing over unions of double cosets, same-size swaps). Output on cost 0: .edges, .T.

Runs (25 s or less each, THREADS=1):
- Z409 x| Z3 (r 53, d 1), Delta 3, D 10 (818 vertices): best cost 1304.
- Z409 x| Z2 (r 408, d 1) (dihedral), D 10: best cost 1556.
- Z199 x| Z3 (r 92), D 10 (398 vertices): cost 464; D 12: cost 326; D 14: cost 164.
- Z241 x| Z3 (r 15), D 10 (482 vertices): cost 632. Z331 x| Z3 (r 31), D 10 (662 vertices): cost 992.
- Z409 x| Z4 (r 143, d 1): no exact |T| = 12 composition (double-coset sizes), infeasible.
- Z409 x| Z3 (r 53, d 1), Delta 3, D 30: cost 0. apsp check (tools/bin/apsp t_test30.edges 3 30):
  n=818, simple, cubic, bipartite, connected, DIAMETER 25. So the metric is right and the family is poor:
  even with 398 vertices the best states have diameter well above 14, where random cubic bipartite graphs of that
  order have diameter about 10-11.
Conclusion: stabilizers in the coset quotient waste words (distinct words collapse on cosets of H), so coset graphs of
Frobenius-type groups are much worse than Haar graphs of the same vertex count. Not a route to (3..6,10).

## Second approach: abelian NON-cyclic voltage lifts (liftab.c = liftd.c with group Z_a x Z_c, env AB="a c")
Base base55.txt = 5+5 cubic bipartite circulant H(Z5,{0,1,2}) (10 vertices), lift = 10n vertices, need n >= 82.
Cost = far pairs from the base sources (same as liftd). Runs (10 to 45 s each, machine load ~20 on 4 cores):
- Z2 x Z42 (n 84): 52 (15 s), 52 (35 s, restart from best)
- Z6 x Z14 (n 84, 840 vertices): 52 -> 34 (35 s), 34 (45 s reheated, two more runs)
- Z2 x Z44 (n 88): 93; Z3 x Z30 (n 90): 74 (15 s), 88 (40 s); Z6 x Z15 (n 90): 104
- 10+10 base rnd10_0 (b = 20, n 44..54): Z2xZ22 159 and cyclic Z44 178 at 35 s
No cost-0 found; closest is Z6 x Z14 at cost 34 (840 vertices, D = 10, not a record).
Files: c55_6_14.best (voltages "edge volt" lines), c55d_6_14.best; the .edges output is written only at cost 0.
