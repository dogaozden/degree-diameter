# r2g (wildcard 2) NOTES

Start: 2026-10-31T17:36:11Z (date -u). Stop about 19:36-19:51Z.

## Idea (chosen)
Exhaustive enumeration of cubic bipartite graphs with a PRESCRIBED NON-FREE colour-preserving permutation group G
(orbit-graph / Potocnik-style census). Sides are unions of G-orbits G/K_i (K_i any subgroup, so stabilisers may be
non-trivial; fixed points allowed). A G-invariant graph is a choice of edge orbits (double cosets K\G/L) with
degree 3 at every orbit. Solved by DFS over edge orbits, every solution scored with an all-pairs bitset BFS.
Why it is new: the excluded classes are free actions (order >= 8 colour-preserving free group excluded at n=170),
prime order >= 11, and vertex/edge-transitive graphs. Non-free groups such as PSL(2,7) (order 168, stabilisers
of order 2,3,4,6,7,8,...) are not covered by any card. Earlier cards only did order-3 fixed points (c5, r2f).

Code: r2g/orb.py (group + subgroup classes + orbit ILP DFS + bitset far).

## Results so far (all graphs scored with ../bin/score37 where logged; far = unordered pairs at distance > 7)
Calibration with PSL(2,7) (order 168, colour-preserving, 15 subgroup classes):
- n=168 (m=84), exhaustive-ish DFS over 2971 of 33k side-composition pairs in 200 s: 291,932 invariant graphs,
  best far 1456 (diam 9). So the PSL(2,7) family is far from diameter 7 at all sampled points.
n=170 (m=85), randomised DFS over compositions (cap 300-5000 graphs per composition):
- S4 (order 24): 60,000 graphs, best far 8038 (lexicographic DFS, not diverse; ignore the exact number).
- A5 (order 60): 135,000 graphs over 9448 compositions, best far 390.
- S3 (order 6, non-free, fixed points allowed): best far 1108 (DFS sample), 223 after orbit-level LNS (150 s).
- V4 = Z2 x Z2 (non-free): census with orbit LNS, 12 composition pairs, best far 288.
- D4 (order 8): 783k compositions, no feasible pair found in 420 s (DFS budget too big; to fix).

Observation: every colour-preserving non-free symmetric family tried is far above the board's 46 at n=170. The
symmetric families are far worse than the unstructured-like searches (far 46 / 76). So the 'non-free group' idea
does not contain good graphs at these sizes, at least for groups of order >= 6 (small groups not yet explored well).

Derived fact (checked by hand, useful to others): for n = 2m with m = 85, diameter <= 7 forces EVERY vertex to have
exactly 127 - m = 42 coincidences among its 127 even NB walks of length <= 6 (the same-side ball is at most m, so the
card's "excess <= delta" is the covering condition R = delta). With girth 12, coincidences at depth 6 are exactly the
12-cycles through the vertex. A 2-switch in a diameter-7 graph always creates a cycle of length <= 8 (opposite-side
pairs are at distance <= 7), so girth-12-preserving local search is rigid and useless for this problem.

## Calibration that passed (18:27Z): conder168 colour-preserving automorphisms
- c5/out/aut168.txt has the 504 automorphisms of C168.1; the colour-preserving subgroup H has order 252 (calib168.py).
- Orbit model with composition [84 orbit, stab order 3] | [84 orbit, other stab class]: 28 edge orbits.
  Random completions by the orbit DFS give far 0 in 134 of 200 samples, i.e. the engine recovers C168.1.
  (An earlier version used the same stabiliser class on both sides and missed it; the B-side stabiliser class
  must be chosen separately, which run.py/census.py do.)

## Later results (18:45-19:28Z)
- H252 census (random compositions, orbit LNS, 400 s): best far 7065 at n=170. Exhaustive K<=3 orbits per side at
  m=85 (exh3.py, 420 s, 18 of 120 pairs, 931k graphs): best far 10584, most graphs disconnected. Not useful.
- Z2 census (fixed points allowed, 400 s, 8 pairs): best far 473. A4 census: 2459. PSL(2,7) census at m=85 (420 s,
  11 pairs): 11564 (disconnected). Random compositions with many fixed points are hopeless; the census needs
  feasibility-aware sampling, which I did not finish.
- Z3 (order 3), orbit LNS with exact DFS completions, n=170 (lns.py, class 0 = fixed point, class 1 = free orbit):
  * 1 fixed point per side: 171 (200 s, seed 3, lns_z3_m85_s3.edges, logged), 201 (330 s, seed 4), 174 (420 s, seed 6).
  * 4 fixed points per side: 183 (300 s, seed 5, diam 9).
  c5's quotient SA reached 78 with Z3 + 3 fixed points, so the orbit-LNS engine is weaker there, not better.
- S3 composition LNS: 223 (seed 1, 150 s), 307 (seed 2, 400 s). Glassy landscape: results depend on the seed.

## Summary (r2g, end 19:30Z)
Engine validated (C168.1 recovered exactly by the H252 orbit model). Every non-free symmetric family tried at n=170
has best far >= 171 (Z3 LNS), with the exception of none. Nothing beats the board's 46 at 170 and nothing beats the
board's 76 at 172, so no record candidate. Negative result: non-free colour-preserving symmetry (groups of order 2 to
252, fixed points allowed) does not produce diameter-7 or near-46 graphs at n=170 under this search.
- Z3, 1 fixed point per side, seed 7 (T0 2.5, T1 0.2, KMAX 2, 330 s): far 165 (lns_z3_m85_s7.edges, logged as r2g best at 170).
  Stopped at 19:34Z (2h elapsed). Best r2g graph at 170: far 165, file r2g/out/lns_z3_m85_s7.edges (verified with bin/score37).
