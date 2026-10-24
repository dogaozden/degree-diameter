# Round d12D7-r1 cards (8 Haiku cards, one squad)

Preamble: PREAMBLE.md. Scoreboard: scoreboard.jsonl. Folders: c1/ … c8/.

**c1 – sheet lift.** Base B = H(q) × Z_3 with two perfect matchings σ, σ′, both of shift +1 (degree q+3, diameter ≤ 7 by the
cover theorem with T = {1}). Lift B by Z_2 with voltages on all edges (hexagon edges in each copy, both matchings): 6·|H(q)|
vertices; at q = 9 this would be 797,160 > 664,300. Opus's partial analysis: same-copy pairs at hexagon distance 6 in the
other sheet need non-coboundary hexagon voltages (their q+1 geodesics must carry both values); a generic same-side
cross-copy pair has 6 routes (3 per matching); random voltages leave about 1–2 % of generic pairs uncovered. Test q = 2, 3, 4
(Δ = 5, 6, 7; 756, 4,368, 16,380 vertices) with a C annealer: state = Z_2 voltage of every base edge (optionally also the
matchings); cost = number of (base vertex s, lifted vertex) pairs at distance > 7 from (s, sheet 0). Score: min cost at
q = 3 (0 = success). If q = 3 reaches 0, try q = 4 and describe any structure in the voltages.

**c2 – lift-lemma falsification.** Base: the record's shape at small q, H(q) × Z_5 with 2 matchings of shifts 1, 2. Lift by
Z_2 with voltages on all edges. Opus's lemma: impossible for q ≥ 3, possible in principle only at q = 2. Test q = 2 (Δ = 5,
1,260 vertices) and q = 3 (Δ = 6, 7,280) by annealing. Also report the distribution of the number of walks of length ≤ 6
between same-side vertices in different copies of the base (Opus claims exactly 3 for most pairs). Score: min cost at q = 3.

**c3 – surgery on polygon covers.** From C = H(q) × Z_{2j+1} + j matchings (q = 3, j = 2: Δ = 6, 3,640 vertices; q = 3, j = 1:
Δ = 5, 2,184; q = 4, j = 1: Δ = 6, 8,190), find any graph with the same maximum degree, D ≤ 7 and more vertices, by local
surgery (delete a few edges or vertices, add vertices, rewire). Opus expects failure for q ≥ 3 (every edge is on the unique
short route of about 5q⁴ pairs); a +1 at q = 3 by a mechanism that does not depend on q would be big (at q = 9, +1 is a
record). Score: best (vertices with D ≤ 7) − baseline, apsp-checked.

**c4 – cubic controllers with hexagons.** Find cubic bipartite graphs of diameter ≤ 7 in which every vertex lies on a 6-cycle
(or a 4-cycle), maximising m = vertices per side. m ≥ 82 would make a route-chart lift over F_4^6 (Δ = 3 letters × 4
scalars = 12, 2·m·4096 vertices) a (12,7) candidate. The only cubic D = 7 graph with 168 vertices is Conder's, girth 12.
Try Haar graphs H(G, {e, a, b}) of groups of order 60–90 with a relation forcing 6-cycles (e.g. (a⁻¹b)³ = e), and lifts
of small cubic bases (2+2, 3+3) with a forced trivial-voltage hexagon. Score: max m (apsp-checked, every vertex on a
≤ 6-cycle).

**c5 – literature and the current table value.** Has the bipartite (12,7) value changed since 2013? (CombinatoricsWiki direct
fetch fails TLS; try search snippets, mirrors, Wikipedia, arXiv 2014–2026.) Any construction beating (2j+1)·|GH(q)| at D = 7
(or (2j+1)·|GQ(q)| at D = 5) in any cell? Delorme–Gómez–Quisquater's unpublished constructions (the D = 8 values 35·|H(9)|
etc.)? URLs and exact quotes; mark what you could not open. Score: largest source-verified (12,7) value (664300 if unchanged).

**c6 – wildcard at (7,7) = 23,436 = 3·|H(5)|.** Any structured construction that is not a random/orbit Haar search, a
polygon cover or a lift of one, a route-chart lift or a building Weyl-distance graph (e.g. coset graphs Cos(G; H, K) with
non-parabolic H, K; Haar graphs with algebraic connection sets; compounding two different polygons; near-polygon
variants). Do the counting check first (same-side walks ≤ 6 at Δ = 7: 55,987; the record needs 11,718, 21 %). Score: largest
order with D ≤ 7, Δ ≤ 7 (apsp), or the smallest uncovered count at an order ≥ 23,438.

**c7 – wildcard at (12,7) directly.** Same exclusions as c6. First a counting argument that your family can exceed 17 %
same-side coverage, then the cheapest experiment that could refute it. Score: best D ≤ 7 order at Δ ≤ 12, or your family's
projected order with the evidence.

**c8 – wildcard: an approach none of the other cards uses** (list of the others: c1 sheet lift; c2 Z_2-lift of the 5-copy
cover; c3 surgery; c4 cubic controllers with 6-cycles; c5 literature; c6 structured ideas at (7,7); c7 structured ideas at
(12,7)). Examples: biregular designs, two hexagon structures sharing vertices, incidence between two different
geometries, a symmetric family with a huge automorphism group searched by computer. Justify by counting, test small.
Score: as c6 or c7.
