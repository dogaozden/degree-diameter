# squad-alone-6: voltage lifts of a circulant bipartite base (Haiku alone, no Opus)

Target: bipartite, max degree 16, diameter 5, more than 31,460 vertices. Table value 27,300.
**Result: not reached. Best verified order 16,000 vertices (all-pairs checked). Below the target and the table value.**

## Construction

- Base graph: circulant bipartite multigraph on k + k vertices, A_i ~ B_{(i+t) mod k} for t = 0..15, so degree 16.
  k = 1 is the Haar dipole. For k = 16 the base is K_{16,16} (offsets 0..15, each once).
- Voltages x[i][t] in G = Z_m x|_r Z_n (element index a*n + j; r^n = 1 mod m). Lift: (i,g) ~ (k + (i+t) mod k, g x[i][t]).
- Gauge: a spanning tree of the base gets voltage e (t = 0 for all i, and t = 1 for i < k-1). This fixes 2k-1 voltages.
- Parallel base edges keep distinct voltages, so the lift is simple (apsp rejects repeated edges).
- Diameter check: left multiplication by G is an automorphism, so dist((u,g),(w,h)) = dist((u,e),(w,g^-1 h)). Only the 2k base sources need a BFS, to depth 5.
- Cost = sum over the 2k sources of lift vertices at distance > 5. Cost 0 = valid.
- Search: simulated annealing on single voltage changes (vlift.c), geometric cooling from T0 to T1. Groups from groups.py.
- Every find is checked by research/lifts/coordinator_check/apsp.c (all pairs, no symmetry assumed). See finds/*.check.txt.

## Results (scoreboard.jsonl has one line per attempt)

| base k | G | N = 2kG | iterations | cost | valid |
|---|---|---|---|---|---|
| 1 | Z_5 x|_2 Z_1200 | 12,000 | 120k | 0 | yes (finds/k1_G6000_s1) |
| 1 | Z_4 x|_3 Z_2000 | 16,000 | 40k | 112 | no |
| 2 | Z_4 x|_3 Z_1000 | 16,000 | 40k | 3 | no (seed 1) |
| 2 | Z_4 x|_3 Z_1000 | 16,000 | 200k | 0 | yes (finds/k2_G4000_s2_long) |
| 4 | Z_5 x|_2 Z_400 | 16,000 | 120k | 0 | yes (finds/k4_G2000_s1) |
| 8 | Z_5 x|_2 Z_200 | 16,000 | 120k | 0 | yes (finds/k8_G1000_s1) |
| 2 | Z_5 x|_2 Z_900 | 18,000 | 300k | 6 | no |
| 2 | Z_5 x|_2 Z_1000 | 20,000 | 200k | 45 | no |
| 4 | Z_5 x|_2 Z_500 | 20,000 | 200k | 65 | no |
| 8 | Z_5 x|_4 Z_250 | 20,000 | 200k | 156 | no |
| 2 | Z_5 x|_2 Z_1200 | 24,000 | 200k | 228 | no |
| 4 | Z_5 x|_2 Z_800 | 32,000 | 40k | 2470 | no |

Two runs were killed by a worker restart before finishing: k=4 at N=18,000 and k=16 at N=19,200 (G = Z_5 x|_4 Z_120). They
have no scoreboard line.

## Why this should not reach 31,460 (counting, not a proof)

- Walks of length <= 4 from a base vertex that end on the same side number about 16 * 15^3 = 54,000, whatever k is
  (the base is locally tree-like, so the walk count does not depend on k). Same-side targets are k*G = N/2. At N = 31,460 that
  is 15,730 targets for about 54,000 walks. A random voltage assignment leaves about e^(-3.4) * 15,730 = ~500 targets
  uncovered per source. That is far from zero.
- Larger k is not better. A voltage assignment has about 14k free voltages in G, but there are 2k sources to cover. So the
  first-moment tolerance per source is about 7 ln(N/k), which shrinks as k grows. Lifts with a big base only add constraints.
- The search results fit this picture. The valid frontier is about 16K for k = 1, 2, 4, 8, and all bases fail between 18K and
  24K (costs 6 to 228). The k = 1 Haar case at N = 16K already fails (cost 112), while the k = 2 case reaches cost 3 at N = 16K.

## What would be needed

Random-like voltages give at most about 16K here. The record constructions must use structure: voltages from a
geometric or algebraic object with few repeated walk values, not random assignments. Searching over metacyclic groups by
annealing does not get there.

## Caveats

- Single annealer, with at most 300k iterations and one or two seeds per configuration. Failures mean "not found with this
  budget", not impossible. Only metacyclic groups were tried, and only circulant bases.
- 16,000 is a verified lower bound from this search, not a claim about the table.
