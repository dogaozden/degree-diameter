# c17 (wildcard): mixed-side hubs. Result: invalid (bipartiteness), score 0

## Idea
Hub capacity in the lab model is K_A + K_B = min_j out_j + min_j in_j, because B-hubs use only A-slots (out-freed
elements) and A-hubs only B-slots. Hypothesis: a hub may take an A-slot or a B-slot in each level, so K <= min_j
(out_j + in_j), which is larger (q=11, types HHHDHDD, c=0: 344 vs 233; q=5 caps 26/21: 68 vs 47).
Hub-hub pairs with different side-patterns are within distance 5 through the level where their slots differ in kind
(1 + d(point,line) + 1 <= 5), so only same-pattern pairs would need Y-edges.

## Why it fails
Each level graph is bipartite with colour(A-element) = 1 and colour(B-element) = 0 for every level (types H/D make
every matching edge bichromatic and every incidence edge bichromatic). So a hub adjacent to an A-slot and to a B-slot
closes an odd cycle. A hub must be on one side only. Checked: level graph at q=5 has 0 colour conflicts; the mixed
graph (K=40) has 786 conflicting edges, and apsp says RESULT INVALID (bipartite=no). The lab bound
min out + min in is therefore forced for hubs of this type.

## Files
- mixed.py: builder (q, r, seed, arcs, types, K, out). cap5.py / tourn.py / capacity.py: bound computations.
- parity.py: colour-conflict check. INVALID_mixed_q5_K40.edges (apsp INVALID).
- q5_levels_only_valid.edges: q=5, r=3, 7 levels, types HHHHDDD on the tournament
  [(0,3),(0,4),(0,6),(1,0),(1,2),(1,5),(2,0),(2,4),(2,5),(3,1),(3,2),(3,5),(4,1),(4,3),(4,6),(5,0),(5,4),(5,6),(6,1),(6,2),(6,3)],
  spreads (26 lines) on D->H arcs, partial ovoid of 18 points on H->D arcs. `./apsp ... 9 5`: RESULT VALID n=2184, bipartite.
  It has no hubs, so gain 0.

## Next
Only same-side hub designs remain (lab bound). Same-side hubs need even distance <= 4 between each pair: via a
collinear pair of slots at some level, or a Y-path. Collinear slots from different out-arcs of one level are one
possible source of this (not tested).
