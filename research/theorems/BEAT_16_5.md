# Beating 31,460 at (Δ, D) = (16, 5), bipartite

Job "beat-16-5" (Opus), branch `claude/beat-16-5-bipartite-px5cxt`. Started 2026-10-24.

**Status (2026-10-24 05:20 UTC): beaten. A 16-regular bipartite graph of diameter 5 on 32,768 vertices**
(`graphs/d16D5_n32768_rcl_g64_43.edges.gz`, all-pairs check `beat165/check_d16D5_32768.txt`: RESULT VALID d=16 D=5
n=32768). It is a bipartite version of Mizuno's route-chart lift (arXiv:2606.15860, a general-graph construction):
controller = a 4-regular Haar graph on SmallGroup(64,43), fiber F₄⁴. Details in §4. Coordinator: please re-check
independently; `beat165/rcl/buildlift.py` rebuilds it from the group table, S and the chart.
## 0. What a winner has to do (counting)

From a vertex, the non-backtracking walks of length ≤ 4 that end on the same side number
1 + 16·15 + 16·15³ = 54,241. Diameter 5 means these reach all N vertices of that side (opposite-side distances
≤ 5 follow). So N ≤ 54,241, and the average number of walks per target is 54,241/N. C(2,3) has
54,241/15,730 = 3.45. A graph with N > 15,730 per side needs fewer than 3.45 walks per target, with no target missed.

For random-like constructions this is far out of reach. The coupon-collector estimate of SIZE_LAW.md gives
μ = N·e^(−54,241/N) expected misses per source: μ ≈ 510 at N = 15,731, while searches solve at μ ≈ 10–40.
The size law puts a random-like Haar graph at (16,5) near N ≈ 9,000–9,500 (about 18,500 vertices), below even the
2013 table (27,300). So Haar search with random-like S cannot get near 31,460; only structure can.

## 1. Buildings: A₄(3) is the only one (checked exhaustively)

### 1.1 Partial-flag graphs ("residues meet")

`beat165/partflags.py`: every finite building of type A₂–A₇, B₂–B₆ (also with parameters (q,…,q,q²), (q²,…,q²,q),
(q²,…,q²,q³)), D₄–D₆, E₆, F₄ (also (q,q,q²,q²)), G₂ (also (q,q³)), q ≤ 16; side A = residues of type J, side B =
residues of type K, J ∪ K = S, adjacent when they meet. Max degree ≤ 16 and diameter ≤ 5: only A₄(3) with
J = {2,4}, K = {1,3} (31,460); every other hit has at most 146 vertices. (D ≤ 7 hits: GH(q), and D₄(3) with
(13,16)-degrees on 81,200 vertices, diameter 6.)

### 1.2 Any union of Weyl-distance classes as the adjacency

`beat165/hecke_cosets.py`: same buildings, side A = J-residues, side B = K-residues for all J, K (overlapping,
empty, equal), adjacency δ(R_A, R_B) ∈ Ω for every union Ω of (W_J, W_K)-double cosets with both degrees ≤ 16.
In a building the Weyl distances reachable by a walk with prescribed steps form the support of the product in
the Iwahori–Hecke algebra (structure constants ≥ 0), so diameter ≤ 5 iff Ω∘Ω⁻¹∘Ω∘Ω⁻¹ = W and Ω⁻¹∘Ω∘Ω⁻¹∘Ω = W.
This is exact, not a sample. Result for A₂–A₄, B₂, B₃ (all parameter sets above), G₂, I₂(8), q ≤ 16, keeping
graphs with ≥ 20,000 vertices: the only one with diameter ≤ 5 is A₄(3) with the flag relation. (331 configurations
with more than 31,460 vertices fail.) Larger types (A₅, A₆, B₄, B₅, D₄, D₅, F₄): running.

## 2. Affine and hyperbolic diagrams: room in the ball, no finite quotient in hand

`beat165/coxball.py`. For a 4-node diagram split {0,2} | {1,3}, the A-vertices within distance 2k of a vertex are the
J-residues at Weyl distance in W_J(W_K W_J)^k, counted by Σ q^ℓ(w)/16. At q = 3, radius 4:

| diagram (labels 01, 12, 23, 30) | radius 2 | radius 4 |
|---|---|---|
| A₄ (3,3,3,2) | 205 | 15,730 (= everything) |
| Ã₃ (3,3,3,3) | 241 | 33,883 |
| C̃₃ (4,3,4,2) | 205 | 28,744 |
| cycle (3,3,3,4) | 241 | 40,714 |
| cycle (4,4,4,4) | 241 | 52,945 |

C(2,3) differs from the Ã₃ flag graph in one place: its {1,4}-residues are K₄,₄ blocks (the source of all its 4-cycles),
where Ã₃ has projective planes. A finite quotient of the Ã₃ building whose flag graph keeps diameter 5 could have up
to 33,883 vertices per side. But it would need to be as "perfect" as a spherical building (each A-orbit hit by
≤ 2.15 ball elements on average, none missed); quotients by arithmetic lattices of PGL(4, F₃((t))) of that size would
be tiny solvable quotients (congruence subgroup property), which cover badly. Not pursued further yet.

## 3. Coset graphs with large stabilizers (in progress)

Why: the counting bound in §0 is an average. In an edge-transitive coset graph Cos(G; H, K) (sides G/H, G/K,
edges G/(H ∩ K), degrees [H : H∩K] and [K : H∩K]) the A-vertices within distance 4 of the base vertex form a union
of H-orbits, so misses come in clumps of size up to |H|. With μ ≈ 500 expected missed vertices at N ≈ 16,000, the
expected number of missed regular H-orbits is about μ/|H|, i.e. about 1 for |H| ≈ 500. The flag graph is the extreme
case (|H| = 15,116,544, 11 orbits per side). So the search space worth trying is: groups G of order ~10⁷–10⁹ with
subgroups H, K of index 8,000–54,241 meeting in a subgroup of index ≤ 16 in both.

Tools (`beat165/gap/`, GAP 4.12 with tomlib):
- `cosetsearch2.g`: for subgroup classes H, K (from a table of marks), every H-orbit of length dA ≤ 16 on G/K
  is a candidate K' = K^g with H ∩ K' = Stab_H(Kg); keep it when dB = [K' : H ∩ K'] ≤ 16. Diameter ≤ 5 iff
  HK'HK'H = G and K'HK'HK' = G, tested in the coset actions with orbit partitions (exact).
- `export.g`: writes the edge list of a coset graph for `apsp` (the coordinator's all-pairs checker, no symmetry).
- Validation: from (P₂₄, P₁₃) in SL(5,3) the search finds the flag graph as the only candidate (balls 205 and 15,730
  on both sides), and the exported edge list passes apsp (RESULT VALID d=16 D=5 n=31460).

## 4. The winner: a bipartite route-chart lift (32,768 vertices)

### 4.1 Construction

Mizuno (arXiv:2606.15860, general graphs, (16,5) ≥ 147,456) lifts a small labeled "controller" graph C to
V(C) × F_q^s: an edge u → v of C with label t (labels come in inverse pairs t, t⁻¹; each vertex has exactly one
outgoing edge of each label) lifts to the q edges (u, x) ~ (v, A_t x + λ b_t), λ ∈ F_q, with A_{t⁻¹} = A_t⁻¹ and
b_{t⁻¹} = A_t⁻¹ b_t. Degree ρq for a ρ-regular controller. Along a controller walk with labels t₁…t_k the endpoint
is A_w x + M_w λ with M_w = [A_{t_k}⋯A_{t₂} b_{t₁} | … | b_{t_k}].

Bipartite version used here: ρ = 4 (labels a, a⁻¹, b, b⁻¹), q = 4, s = 4, so degree 16 and |V| = 256·|C|.
The lift is bipartite when C is. Diameter ≤ 5 iff for every same-side pair of controller vertices (c, d) and every
x, the union over controller walks w from c to d of length 0, 2 or 4 of the affine sets A_w x + Im M_w is all of F₄⁴
(opposite-side distances are then ≤ 5 automatically). What makes this work:
- pairs at controller distance 4 are covered by one geodesic once M_w is nonsingular for every label-reduced
  word of length 4 ("universal chart"; found in seconds by annealing, `rcl/chart4.c`);
- pairs at distance 2 can be covered by walks with one back-and-forth excursion: they all have the same linear part
  and their images are 3-spaces through the plane P = span{A_{t₂} b_{t₁}, b_{t₂}}, and the five hyperplanes through
  P cover F₄⁴. So no 6-cycles are needed in the controller, only the right chart;
- a vertex c with itself needs a 4-cycle through c (the backtracking closed walks cover at most 70 of the 85
  projective points), so the controller must have a 4-cycle at every vertex.

So the controller only needs: bipartite, 4-regular, diameter 5, a 4-cycle at every vertex. Haar graphs H(G, S),
|S| = 4, are vertex-transitive on each side, so one 4-cycle (a repeated quotient s_i⁻¹s_j = s_k⁻¹s_l) suffices.
`rcl/haarctrl.c` scans all groups of a given order exhaustively; order 64 has 6 such (G, S) (first ones at 40, 50,
60; none at 62, 63).

**Lemma (bipartite route-chart lift).** Let C be a bipartite graph whose edges carry labels from {a, a⁻¹, b, b⁻¹}
so that every vertex has exactly one outgoing edge of each label and the reverse of an a-edge is an a⁻¹-edge (the
same for b); equivalently two permutations σ_a, σ_b of V(C) that swap the sides. Let A_a, A_b ∈ GL₄(F_q) and
b_a, b_b ∈ F_q⁴, with A_{t⁻¹} = A_t⁻¹ and b_{t⁻¹} = A_t⁻¹ b_t. The lift L has vertex set V(C) × F_q⁴ and edges
(u, x) ~ (σ_t(u), A_t x + λ b_t) for t ∈ {a, b}, λ ∈ F_q. Then:
1. L is bipartite and every vertex has degree at most 4q (exactly 4q when the 4q neighbours are distinct).
2. For a controller walk W from c to d with label word t₁…t_k, the lift walks above W starting at (c, x) end
   exactly at the points A_W x + M_W λ, λ ∈ F_q^k, where A_W = A_{t_k}⋯A_{t₁} and M_W has columns
   A_{t_k}⋯A_{t_{i+1}} b_{t_i} (i = 1..k).
3. diam L ≤ 5 iff for every ordered pair (c, d) of controller vertices on the same side and every x ∈ F_q⁴,
   ⋃_W (A_W x + Im M_W) = F_q⁴, the union over controller walks W from c to d of length 0, 2 or 4.

*Proof.* (1) is clear from the definition (the reverse of the lifted a-edge is the lifted a⁻¹-edge with −λ). (2) by
induction on k. (3) Two lift vertices on the same side are at distance ≤ 4 iff some lift walk of length 0, 2 or 4
joins them; it projects to a controller walk of the same length, and by (2) the endpoints of the lifts of W from
(c, x) are A_W x + Im M_W. So the condition is exactly "same-side distance ≤ 4". For opposite sides, (c, x) and
(d, y) with y' a neighbour of (d, y) on the side of (c, x): the distance is ≤ 1 + d((c, x), y') ≤ 5. ∎

The searches use (3) directly: `chartfit2.c`, `chartfit3.c`, `fitq.c` compute the number of (c, d, x, y) violating
it exactly, by enumerating the ≤ 273 label words of length 0, 2, 4 per controller pair. For a vertex-transitive
controller (Haar, permutation-voltage) it suffices to take c in one orbit representative per orbit.

### 4.2 The graph

- Controller: H(G, S) with G = SmallGroup(64,43) (C₈ . (C₄ × C₂)), elements numbered as in GAP's
  `AsSSortedList(SmallGroup(64,43))` from 0 (table `rcl/g64_43_table.txt`, structure and S as permutations in
  `rcl/g64_43_info.txt`), S = {s₁, s₂, s₃, s₄} = {0, 1, 2, 29}. Vertices (g, A), (g, B); label a: (g,A) → (s₁g, B),
  (h,B) → (s₂⁻¹h, A); label b: (g,A) → (s₃g, B), (h,B) → (s₄⁻¹h, A); a⁻¹, b⁻¹ are the inverse maps.
- Chart over F₄ = {0, 1, ω, ω²} coded 0,1,2,3 (addition = XOR of codes): `rcl/chart_g64_43.txt`
  = A_a rows, b_a, A_b rows, b_b = `3212 1003 2222 3231 | 1023 | 3300 2001 2311 3011 | 0333`.
- Lift vertex (c, x) ↦ c·256 + index of x (x ∈ F₄⁴ in lexicographic order); side A first.
- 32,768 vertices, 262,144 edges, 16-regular, bipartite, diameter 5 (all pairs, apsp). Uncompressed sha256
  18fb910749f631fd6adcf883578c043125344c70fd9ba68548e85d2b98049a26.

How it was found: the six order-64 controllers with the universal chart alone gave diameter 6 (each source fiber
missed 3 of its 64 same-side controller targets). `rcl/chartfit2.c` anneals the chart on the exact number of missed
(x, y) pairs over all same-side targets of the two base vertices (exact for these vertex-transitive lifts; it
reproduced the BFS count 188,928 for the first chart) and reached 0 for SmallGroup(64,43) within 90 s.

### 4.3 Independent rebuild

`rcl/rebuild_gap.g` rebuilds the graph in GAP from the definition alone (GAP's own SmallGroup(64,43) elements and
GF(4) arithmetic; shares only the 40 chart digits and S with the Python builder). The sorted edge list is identical
(sha256 of sorted lists 8cfe42ec…aec1fce for both) and apsp gives RESULT VALID d=16 D=5 n=32768
(`check_d16D5_32768.txt`).

### 4.4 Why 64 per side, and what limits the next step

- Each controller vertex needs a closed label-reduced walk of length 4 (a 4-cycle): proved above (backtracking
  closed walks reach at most 70 of the 85 projective points of the fiber). So the controller is a bipartite
  4-regular graph of diameter 5 with a 4-cycle at every vertex; |V| = 256·|C|.
- Haar controllers H(G, S), |S| = 4: exhaustive over all groups of orders 40–121 (`rcl/haar_summary.txt`). With a
  4-cycle and diameter 5 they exist at orders 40, 50, 60 and 64 and at no order 65–121. 64 is the Haar maximum.
- The (4,5) bipartite record without the 4-cycle condition is 162 (81 per side; it has girth 6). A controller
  with 65–81 per side and 4-cycles everywhere would give 33,280–41,472. Searches running: permutation-voltage
  lifts of 2+2, 3+3, 4+4 bases by all groups of orders 33–48, 22–32, 17–24 (`rcl/pvctrl.c`, `rcl/run_pv.sh`);
  direct annealing of 4-regular bipartite graphs (`rcl/anneal45.c`) is too weak (stuck at ~80 violations at 50
  per side).
- The chart: per-controller fitting (`rcl/chartfit2.c`, `rcl/chartfit3.c` for any permutation-voltage controller)
  is exact and fast. A chart that works for every such controller (universal + the distance-2 hyperplane condition
  for all 12 label pairs) was not found (annealing stops at 4 violations); the winning chart has 14 singular words
  and fails the distance-2 condition for labels bb and BB, and the controller's other walks cover those pairs.

### 4.5 Going past 64 per side (in progress)

- Permutation-voltage controllers (base with k+k vertices, lifted by a group of order m; Haar = k 1): with k = 3
  and the cyclic group of order 22 there are bipartite 4-regular diameter-5 controllers with a 4-cycle at every
  vertex and **66 per side** (5 found, `rcl/pv_found_k3.txt`). They would give 33,792. But fitting a chart is
  hard for them: each has 14 "deficient" same-side pairs (distance 2, no non-backtracking 4-walk), with label
  patterns that include same-letter ones (aa, AA, bb, BB), so the chart needs the distance-2 hyperplane condition
  for nearly all 12 patterns plus few singular words. Restart-based fitting (`rcl/chartfit4.c`) is at 130k–330k
  missed pairs so far. For the order-64 Haar controller only 6 pairs were deficient, all with mixed patterns.
- Field charts (A_a, A_b = multiplication by α, β in F₂₅₆ = F₄⁴, b_a = 1, b_b = γ): exhaustive over all
  255³ triples (`rcl/chartfield.c`). The best universal ones fail the distance-2 condition for all 12 patterns
  (each reaches only 2 of the 5 hyperplanes). So good charts must be non-commutative.
- New approach: fix a chart, export which 108 words are nonsingular and which of the 12 patterns pass the
  distance-2 condition (`rcl/charttables.c`), and search controllers whose every same-side pair is certified
  (a nonsingular non-backtracking 4-walk, or a 2-path with a passing pattern; `rcl/pvctrl2.c`). Certified
  controllers need no fitting; checked on an order-64 example (apsp VALID). Running for k = 2, 3, 4 at 66–96 per
  side with the chart of §4.2 (94 good words, 10 good patterns).

### 4.6 More controller families (negative so far)

- Bipartite Cayley controllers Cay(Γ, {a^±1, b^±1}) with a, b outside an index-2 subgroup Γ₀: need all words of
  length ≤ 4 to cover Γ₀ and one reduced relation of length 4. Exhaustive over all groups of orders 120–190 and
  all generator pairs (`rcl/ctrlsearch2.c`, `rcl/cay_summary.txt`): no hit at any order, including 128 (64 per
  side, where Haar controllers exist). Earlier, with the stronger exact-NB-4 condition, the largest was 36 per side.
- Constraint view of the 66-per-side controllers: per controller there are about 270–300 sets of words of which
  one must be nonsingular (pairs at distance 4 or 0 with at most 4 candidate words) and about 60 distance-2 pairs
  that need a nonsingular word or a passing pattern (`rcl/critical.py`, `rcl/chartcrit.c`). Best charts so far
  violate 132 and 176 weighted constraints. The order-64 Haar controller has only 98 such sets.
- Near-miss pipeline: chart-aware controller search for the chart of §4.2 (objective = uncertified same-side pairs),
  then the exact fitter on the best controller (`rcl/near_miss.sh`). Running for k = 2 (C₃₃) and k = 3 (C₂₂).

### 4.7 A lead for other cells (not pursued here)

The lift works for any degree ρq with ρ even (ρ labels in inverse pairs) and fiber F_q⁴, giving 2·(controller
side)·q⁴ vertices at diameter 5. Over F₃ the closed-walk obstruction of §4.1 disappears by counting (backtracking
closed walks can reach up to 52 ≥ 40 projective points), so for (12,5) = 4·3 any bipartite (4,5) controller might
do: the order-64 Haar controller would give 10,368 and the 162-vertex (4,5) record 13,122, against the table's
8,200. With odd ρ one needs involution labels (A_t² = I, A_t b_t = b_t); then (15,5) = 5·3 and (9,5) = 3·3 come into
range of the (5,5) and (3,5) records (2·177·81 = 28,674 vs 20,496; 56·81 = 4,536 vs our 2,662). None of this is
built or checked; a chart fit for (12,5) on the order-64 controller is running at low priority.
