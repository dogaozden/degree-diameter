# The (Δ,8) table construction ΩB₁ has diameter 9 (cell-12-8 job, round 2, 2026-10-25)

Preliminary note, written as soon as it was found; the full write-up follows in research/squads/cells/d12D8.md.

## Source of the table value
The CombinatoricsWiki bipartite table (read over http, which works from the container; https fails) colours (10,8),
(11,8), (12,8), (14,8), (16,8) green: "Graphs found by C. Delorme, J. Gómez, and J. J. Quisquater", reference
"On large bipartite graphs", submitted. The construction is in J. Gómez's PhD thesis (UPC 1986), public at
https://web.mat.upc.edu/francesc.comellas/delta-d/papers/Gomez1986-PhD-red.pdf, section 2.9.3, thesis pp. 44–46
(PDF pp. 50–52), Figures 2.21a/b. The list on thesis p. 46 gives exactly the table values:
ΩH₅ N(8,8) ≥ 195,300; ΩH₇ N(10,8) ≥ 1,176,480; ΩH₈ N(11,8) ≥ 2,246,940; ΩH₉ N(12,8) ≥ 4,650,100;
ΩH₁₁ N(14,8) ≥ 14,172,480; ΩH₁₃ N(16,8) ≥ 36,201,060.

## The construction (as read from the thesis)
B₁ bipartite, even diameter D₁, N₁ vertices, degree Δ₁; Δ₁ + 2 = 2α + β. Take 5α copies of B₁ (α groups of 5) and,
for every vertex t of B₁, 5 new vertices (t,k), k ∈ Z₅ (the thesis's "10 sets of N₁/2 vertices"). In a group of
type (a) (Fig. 2.21a) the new vertex of a point t is joined to the copies of t in copies k−1, k+1 of the group and the
new vertex of a line t to copies k+2, k+3; in type (b) (Fig. 2.21b) points use k+3, k+4 and lines k−1, k+1. So every
copy vertex gets 2 new edges and every new vertex gets degree 2α. N = 5(α+1)N₁, Δ = Δ₁ + 2. The thesis claims
D ≤ D₁ + 2 (= 8 for the hexagon H(q), D₁ = 6). For Δ = 12: B₁ = H(9) incidence graph, α = 6, 30 copies + 664,300
new vertices = 4,650,100.

## Why the diameter is 9, not 8
A new vertex (t,k) is adjacent only to copies of t, and only in 2α of the 5α copies. Let v be a vertex opposite t
in B₁ (distance D₁ = 6) and j a copy not adjacent to (t,k). Any path from (t,k) to v in copy j starts with an edge to
a copy of t, must change copy at least once (every change goes through a new vertex: 2 edges), and its projection to
B₁ runs from t to v (≥ 6 edges). So the distance is ≥ 1 + 2 + 6 = 9 = D₁ + 3. This does not depend on how the copies
are wired, only on the new vertices having degree < number of copies.

## Checks (research/d12D8/r2/mk_omega.py builds the graph; apsp = research/lifts/coordinator_check/apsp.c)
- q = 3 (Δ = 6, α = 3, 14,560 vertices, groups aab): all-pairs diameter 9; the only pairs at distance 9 are
  (new vertex, copy vertex) pairs (ecc.py: 2,187 = 9 non-adjacent copies × 243 opposite vertices from each new vertex).
- q = 5 (Δ = 8, α = 4, 195,300 vertices = the thesis's ΩH₅): all-pairs `apsp om5.txt 8 9` → diameter 9.
- q = 9 (Δ = 12, α = 6, 4,650,100 vertices, groups aaabbb): BFS from new vertex 3,985,800 (eccs.c): eccentricity 9,
  1,062,882 vertices at distance 9 (= 18 non-adjacent copies × 59,049 opposite vertices); from copy vertex 0:
  eccentricity 9 (177,147 vertices at distance 9).
