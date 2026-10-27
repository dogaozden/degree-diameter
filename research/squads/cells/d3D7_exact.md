# Cell (Δ, D) = (3, 7): exact results (job exact-3-7)

Opus session on branch `claude/bipartite-3-7-exact-zpbiyd`, Oct 27 2026. Brief (Doğa): turn the open cell into
mathematical questions: what is the largest bipartite graph of maximum degree 3 and diameter 7? Earlier search
jobs (branches `claude/bipartite-d3-d7-search-9kfg4g`, `claude/bipartite-4-8-squad-zmk3qt`,
`claude/own-small-cells-dkwo42`; notes in `research/squads/cells/d3D7.md` on the first) found nothing above 168.

Every result below is labelled **Theorem** (proof given or cited), **Computer-checked** (exhaustive computation,
validated as described) or **Heuristic**. Tools: `research/d3D7exact/` (README there).

## Summary

| statement | status |
|---|---|
| 168 ≤ N_b(3,7) ≤ 248 | Theorem (168: C168.1; 248: Feria-Purón and Pineda-Villavicencio 2012). Not improved here. |
| For n ≥ 170 the problem is about cubic graphs: n odd ≥ 171 impossible, n ≥ 172 forces cubic, n = 170 reduces to cubic | Theorem (§2.2) |
| Diameter ≤ 7 is a local condition: every vertex has at most 127 − n/2 "excess" walks within radius 6 | Theorem (§2.3) |
| Girth: n ≥ 194 ⇒ g ≥ 6; n ≥ 226 ⇒ g ≥ 8; n ≥ 242 ⇒ g ≥ 10; n = 250, 252 ⇒ g = 12 | Theorem (§2.4) |
| n = 248: structure of 10-cycles and 12-cycles (10-cycles disjoint, spokes, Rep(y) = N(y′), ...) | Theorem (§2.6), partial; n = 248 itself is still open |
| No graph on n ≥ 169 vertices has an automorphism of prime order p ≥ 11 | Computer-checked (§3) |
| Order 7: see §3.3 (results for n = 182, 210, 224, 238 when the runs finish) | Computer-checked / running |
| Order 5, and order 7 at n = 196: not done (estimated 10^9–10^12 search nodes) | Heuristic estimate (§4) |

So a bipartite (3,7)-graph on more than 168 vertices, if it exists, is cubic, has 170 ≤ n ≤ 248, and its automorphism
group has order 2^a 3^b 5^c 7^d (with d = 0 for the values of n settled in §3.3).

## 1. Literature

Sources found by a literature agent and by me (Oct 27, 2026). VBM = recomputed by the agent.

**Who found 168.** CombinatoricsWiki, "The Degree Diameter Problem for Bipartite Graphs"
(http://combinatoricswiki.org/wiki/The_Degree_Diameter_Problem_for_Bipartite_Graphs; the https site has a broken
certificate). The table is "as of January 2012"; the (3,7) cell is 168 in the first revision (17 Jan 2012, by
G. Pineda-Villavicencio) and in the last one (18 Feb 2022). Its colour key: "Graph found independently by M. Conder
and R. Nedela, by C. Delorme, J. Gómez and J. J. Quisquater, and by Eyal Loz." The wiki cites Conder–Nedela, "A more
detailed classification of symmetric cubic graphs" (2006 preprint; published as "A refined classification of
symmetric cubic graphs", J. Algebra 322 (2009) 722–740) and Delorme–Gómez–Quisquater, "On large bipartite graphs"
("submitted"; not found anywhere). So "Conder–Nedela, also DGQ and Loz" in our notes means three independent finds.

**The graph.** It is C168.1 in Conder's census of cubic arc-transitive graphs
(http://www.math.auckland.ac.nz/~conder/symmcubic10000list.txt: "C168.1 : |Aut(X)| = 504 : Type 1 : Girth 12 :
Diameter 7 : Bipartite"); it was already in the Conder–Dobcsányi list to 768 vertices (2002). It is 1-arc-regular,
girth 12, |Aut| = 504; the automorphism group is solvable (derived series 504 > 84 > 4 > 1; VBM by coset enumeration
from Conder's presentation). In Wedd's list it is F168E. Earlier lab work rebuilt it as a lift of the 2+2 base over
C2 × (C7 ⋊ C3) (`seeds/conder168.edges` on the d3D7 branch). Found by searching a census of symmetric graphs, not by a
construction aimed at the problem.

**Censuses (VBM).** In Conder's arc-transitive census to 10,000 vertices the largest diameter-7 graphs have 168
vertices (C168.1 bipartite, C168.4 not bipartite). In Conder's semisymmetric census to 10,000 vertices only three
graphs have diameter ≤ 7 (54, 126, 110 vertices). A cubic graph of diameter 7 has at most 382 vertices, so these
censuses are complete for the question: **every edge-transitive cubic graph of diameter 7 has at most 168 vertices**.
The vertex-transitive census (Potočnik–Spiga–Verret) also stops at 168 for diameter 7 (the d3D7 branch rescanned it).

**Upper bounds.**
- Moore bound: 254 (per side 127). No bipartite Moore graph of diameter 7 (Feit–Higman 1964; Singleton 1966).
- Defect 2 (n = 252): impossible for D ≥ 4 (Delorme–Jørgensen–Miller–Pineda-Villavicencio, EJC 30 (2009);
  Pineda-Villavicencio, J. Algebraic Combin. 34 (2011)).
- Defect 4 (n = 250): impossible for Δ ≥ 3 and odd D ≥ 5 (Feria-Purón and Pineda-Villavicencio, "On bipartite
  graphs of defect at most 4", Discrete Appl. Math. 160 (2012) 140–154, arXiv:1010.5651, Theorem 5.2). Odd defects
  are impossible since such graphs are regular (their Prop. 3.1). Their Prop. 6.5: N_b(3, D) ≤ M_b(3, D) − 6 for
  D ≥ 5, D ≠ 6, so **N_b(3,7) ≤ 248**. (The brief's 252 was out of date.)
- The wiki's upper-bound table has 248 for (3,7) ("Moore bound minus 6"). Feria-Purón's PhD thesis (Newcastle,
  March 2015, "Large interconnection networks with given degree and diameter", Prop. 4.17 on p. 65) has the same
  bound. No later improvement found (citation lists of arXiv:1010.5651 and 1203.3588, searches for defect 6/8).
- Their proof for n = 250 shows every vertex lies on exactly two 12-cycles, so there are 2n/12 of them, and
  2·250/12 is not an integer. At n = 248 the analogous count (3 twelve-cycles per vertex) gives 62, an integer;
  §2.6 explains why the argument does not simply extend.

**Cages.** (3,12)-cage: the generalized hexagon GH(2) incidence graph, 126 vertices, unique (Benson 1966); it has
diameter 6. (3,13): 202 ≤ n ≤ 272; (3,14): lower bound 260 (Exoo–McKay–Myrvold–Nadon, J. Discrete Algorithms 9
(2011); the 2013 and 2026 tables still show 258). Not needed below: girth ≥ 14 would force n = 254 anyway (§2.4).

**Exhaustive enumerations.** None found for cubic bipartite graphs of diameter 7 or girth ≥ 12 between 128 and 250
vertices. Jørgensen's papers (DAM 1992, Discrete Math. 114 (1993)) treat D ≤ 5 ((3,5) = 56 is optimal).

**General cubic graphs, D = 7 (not bipartite, for context).** Comellas' live table lists 200 (Bhakar, Oct 2026; not
bipartite, girth 8, VBM), upper bound 376.

## 2. Theorems

Notation: G bipartite with sides A, B, maximum degree 3, diameter ≤ 7. NB walk = non-backtracking walk (never
reverses the edge just used). For a vertex v, the "positions" are the NB walks from v of even length ≤ 6; in a
cubic graph there are 1 + 6 + 24 + 96 = 127. Same-side distances are even, opposite-side distances odd.

### 2.1 Moore bound (Theorem, classical)

If G is cubic, every vertex sees at most 127 same-side vertices within distance 6, and diameter ≤ 7 means it must see
its whole side; so |A|, |B| ≤ 127 and n ≤ 254. (For D odd, same-side distance ≤ 6 implies opposite-side distance ≤ 7:
go to a neighbour of the target.)

### 2.2 Above 169 vertices only cubic graphs matter (Theorem)

(a) If |A| > |B| then n ≤ 169. (b) If |A| = |B| and G is not cubic then n ≤ 170, and at n = 170 one can add a perfect
matching between the degree-2 vertices of A and of B and get a cubic bipartite graph of diameter ≤ 7 on the same
vertex set. Hence every (3,7)-graph with n ≥ 172 is cubic, n odd ≥ 171 is impossible, and N_b(3,7) ≥ n ≥ 170 iff a
cubic one exists on n vertices. (Also FP–PV Prop. 3.1 for n ≥ 192.)

Proof. (a) Σ_{a∈A} deg a = Σ_{b∈B} deg b ≤ 3|B| < 3|A|, so some a ∈ A has degree ≤ 2. From a, at most
1 + 4 + 16 + 64 = 85 vertices of A lie within distance 6 (at most 43 if deg a = 1), and all of A must. So
|A| ≤ 85, |B| ≤ 84. (b) A vertex of degree ≤ 2 bounds its side by 85 as in (a), so n ≤ 170. At n = 170 the bound is
attained by every deficient vertex x: deg x = 2, its radius-6 ball is a tree and every vertex at distance 1..5 from x
has degree 3. So two deficient vertices are never adjacent. The total deficiency is the same on both sides
(equal edge counts, equal sides), each deficient vertex has deficiency 1, so a perfect matching between the deficient
vertices of A and of B adds only new edges. Adding edges does not increase distances. ∎

Remark: the matching in (b) can be chosen invariant under any automorphism of odd prime order (match orbit to orbit),
which is used in §3.

### 2.3 Diameter 7 is a local condition (Theorem)

Let G be cubic bipartite with |A| = |B| = m, and define the excess of v as R(v) = 127 − #(same-side vertices within
distance 6 of v) = (number of positions) − (number of distinct endpoints). Then R(v) ≥ 127 − m for every v, and
**G has diameter ≤ 7 iff R(v) ≤ 127 − m for every vertex v**; then R(v) = δ := 127 − m everywhere. R(v) depends only
on the ball of radius 6 around v. (Proof: v sees all of its side iff its 6-ball contains m same-side vertices.) For
n = 248, 246, 244, 242 the target is δ = 3, 4, 5, 6 excess walks at every vertex.

### 2.4 Cycle lemma and girth (Theorem)

**Lemma.** If v lies on a cycle of length 2ℓ ≤ 12, then v sees at most 127 − c(ℓ) same-side vertices within
distance 6, where c(6), c(5), c(4), c(3), c(2) = 1, 3, 7, 15, 31.

Proof. Let C = (c_0 = v, c_1, ..., c_{2ℓ−1}), x = c_ℓ, w1 = (c_0, ..., c_ℓ), w2 = (c_0, c_{2ℓ−1}, ..., c_ℓ). Let S be
the set of positions that extend w2 (the subtree of w2) together with those that extend w1·(c_ℓ → c_{ℓ+1}) (the
"back branch" of w1). Every same-side vertex y within distance 6 is the endpoint of a position outside S: take a
geodesic g from v to y. A geodesic cannot extend w1·(c_ℓ → c_{ℓ+1}), since it would reach c_{ℓ+1} at step ℓ+1 > ℓ−1
≥ d(v, c_{ℓ+1}). If g = w2·s, then s does not start with c_ℓ → c_{ℓ−1} (that vertex is at distance ≤ ℓ−1), so w1·s is
an NB walk of the same length and endpoint, outside S. Hence #same-side vertices ≤ 127 − |S|. A subtree rooted at
depth j has Σ_{i even, j ≤ i ≤ 6} 2^{i−j} same-side positions; |S| = that number for j = ℓ plus for j = ℓ + 1. ∎

**Girth table.** With m = n/2, a cycle of length 2ℓ ≤ 12 forces m ≤ 127 − c(ℓ). So:

| n | girth |
|---|---|
| ≥ 194 (m ≥ 97) | ≥ 6 |
| ≥ 226 (m ≥ 113) | ≥ 8 |
| ≥ 242 (m ≥ 121) | ≥ 10 |
| 250, 252 | 12 (and these are impossible by §1) |

Girth ≥ 14 makes every 6-ball a tree, so m = 127; hence girth ≤ 12 for n ≤ 252 (no cage bound needed).

The same proof gives an injectivity statement used in §2.6: **if m = 127 − c(ℓ) exactly, the positions outside S
have pairwise distinct endpoints.**

### 2.5 Two general tools (Theorem)

**(a) Repeat matrix.** Let P(x) = x^6 − 10x^4 + 24x^2 − 8 = F_0 + F_2 + F_4 + F_6, where F_i(A) counts NB walks of
length i (F_0 = 1, F_1 = x, F_2 = x^2 − 3, F_{i+1} = xF_i − 2F_{i−1}). For G cubic bipartite with diameter ≤ 7,
P(A) = J_A ⊕ J_B + E with E a symmetric non-negative integer matrix with row sums δ (E(u, v) = number of NB walks
of even length ≤ 6 from u to v, minus 1). E commutes with A, because A commutes with P(A) and with J_A ⊕ J_B (G is
regular with equal sides). In words: for u, w on opposite sides, Σ_{y∼u} E(y, w) = Σ_{z∼w} E(u, z)
("every repeat of u has a neighbour that repeats each neighbour of u", cf. FP–PV Cor. 4.1). Spectrally, every
eigenvalue λ ≠ ±3 of G satisfies |P(λ)| ≤ δ. (Checked: P(3) = 127; the roots of P are ±2√2 cos(jπ/7).)

**(b) Prime-order automorphisms.** An automorphism σ of prime order p ≥ 5 of a connected graph with maximum degree 3
fixes no vertex (a fixed vertex has its ≤ 3 neighbours fixed, since orbits have size 1 or p > 3), preserves the two
sides (p is odd), and its edge orbits have size p. So G is a regular Z_p-cover (voltage lift) of the quotient
G/⟨σ⟩, a connected bipartite multigraph without loops, with 2k vertices where n = 2kp; for cubic G the quotient is
cubic. Conversely every such lift has the semiregular automorphism (x, g) ↦ (x, g + 1).

Remarks. An LP over spectral measures (support in {|P(λ)| ≤ δ}, tree moments up to the girth) cannot beat the Moore
bound: the measure of the hypothetical generalized heptagon satisfies all of it. The Moore case dies by integrality
(Feit–Higman), and I found no integrality obstruction for δ ≥ 3 (for δ ≥ 3 the set {|P(λ)| ≤ δ} has capacity
(δ/2)^{1/6} > 1, so it holds infinitely many conjugate sets of algebraic integers). Heuristic remark, not a theorem.

### 2.6 Structure at n = 248 (Theorem; partial)

Let G be a cubic bipartite graph of diameter 7 on 248 vertices (m = 124, δ = 3). By §2.4, girth ≥ 10. Call v
**type T** if it lies on a 10-cycle, **type S** otherwise. For type S, let a(v) = number of type-T neighbours.

1. **A type-T vertex lies on exactly one 10-cycle and on no 12-cycle.** Its three excess walks are the two 6-walks
   around its 10-cycle C (to the vertices at C-distance 4) and one of the two geodesics to the third neighbour of its
   antipode on C. Proof: m = 124 = 127 − c(5), so by the injectivity statement in §2.4 the positions outside the
   3-element set S of C have distinct endpoints. A second 10-cycle C′ or a 12-cycle through v would produce two
   positions with a common endpoint, one of them in S; checking the three elements of S, this forces C′ ⊆ C ∪ {y},
   impossible, or a third geodesic to the same endpoint, also impossible.
2. **10-cycles are pairwise vertex-disjoint** (from 1).
3. **The third neighbour ("spoke") of every type-T vertex is type S.** Proof: let C = (c_0, ..., c_9), y_i the spoke of
   c_i. From y_0 the vertex c_5 is at distance 6 with two geodesics (through c_0, both ways round C); distance 4 would
   put c_5 on a second 10-cycle. If y_0 were on a 10-cycle C′, item 1 for y_0 says its only doubly-reached vertex is
   the spoke of its antipode z on C′, so c_5 is that spoke, z = y_5, and c_0 → c_5 (along C) → y_5 → y_0 (along C′)
   → c_0 is a 12-cycle through c_0, contradicting item 1.
4. **For type-S vertices, a(v) ∈ {0, 1, 3}.** Two geodesics from a type-S vertex to a common vertex are either
   internally disjoint (a 12-cycle through v) or share exactly their first edge (a 10-cycle through that neighbour).
   A type-T neighbour u contributes exactly one doubly-reached vertex (u's antipode on its 10-cycle). If a(v) = 2, every
   12-cycle through v would pass through a type-T vertex, so v's excess is 2 < 3. If a(v) = 3, v lies on no
   12-cycle. If a(v) = 1, v lies on exactly two 12-cycles, both through its two type-S neighbours. If a(v) = 0, v lies
   on 3 twelve-cycles (three doubly-reached vertices) or on 4 (it is a branch vertex of a Θ_6 and has one more
   12-cycle).
5. **Spoke pairs.** With C and y_i as in 3, the commutation rule of §2.5(a) applied at c_0 (whose E-row is known by
   item 1: E(c_0, ·) = 1 exactly at c_4, c_6, y_5) gives
   E(y_0, w) = |N(w) ∩ {c_4, c_6, y_5}| − [w ∈ {c_5, c_7, y_6}] − [w ∈ {c_3, c_5, y_4}] for all w, hence
   **Rep(y_0) = N(y_5)**: the three vertices that y_0 reaches twice are exactly the three neighbours of y_5. It follows
   that a(y_0) = a(y_5) ∈ {1, 3}. In the case a = 3, y_0 and y_5 are joined to antipodal pairs of three disjoint
   10-cycles. In the case a = 1, writing N(y_0) = {c_0, z_1, z_2} and N(y_5) = {c_5, s_1, s_2}, y_0 lies on exactly two
   12-cycles (through z_1 y_0 z_2, antipodes s_1 and s_2) and y_5 on exactly two (through s_1 y_5 s_2, antipodes z_1
   and z_2).
6. **If G has no 10-cycle** (girth 12), every vertex lies on 3 or 4 twelve-cycles (item 4 with a = 0), so there are
   between 62 and 82 twelve-cycles; the divisibility argument that kills n = 250 gives no contradiction here.

Items 1–6 make n = 248 look like a rigid configuration problem (every vertex has exactly three excess walks, coming
from one 10-cycle or from 12-cycles in the ways listed), but I did not finish the case analysis, so **N_b(3,7) ≤ 248
stands**. Settling n = 248 would need either the full propagation (items 5–6 propagate along the graph through the
commutation rule) or a computer search built on these rules.

## 3. Computer-checked: automorphisms of prime order

### 3.1 Method

By §2.2 and §2.5(b), a (3,7)-graph on n ≥ 169 vertices with an automorphism of prime order p ≥ 5 is (after the
order-preserving completion at n = 170) a cubic Z_p-lift of a cubic bipartite multigraph on k + k vertices,
n = 2kp, 170 ≤ n ≤ 248. (n = 169 is impossible: orbits of size p would have to divide both 85 and 84.)

Two independent exhaustive programs:

- **`zplift`** (all bases listed by nauty: `nauty-genbg -cq -d1:1 -D3:3 k k | nauty-multig -q -r3 -m3 -T`;
  1, 3, 6, 16, 59, 243, 1,207, 6,979, 45,687, 335,178 bases for k = 2..11). Voltages are 0 on a spanning tree
  (gauge), free on the k + 1 other edges, and the first nonzero one is 1 (scaling by a unit of Z_p). A lift has
  diameter ≤ 7 iff, from every base vertex u, the 127 NB walks of even length ≤ 6 hit all kp pairs
  (same-side vertex, voltage), i.e. iff the number of collisions is at most δ = 127 − kp at every u. Walks are
  linear forms in the free voltages; the search assigns voltages one at a time and prunes as soon as the walks already
  determined collide more than δ times at some u, or some pair (u, v) has fewer than p distinct walk forms left.
  Bases are skipped when some same-side pair (u, v) has fewer than p NB walks between them ("walkcount") or when walks
  with identical forms already give more than δ collisions.
- **`jsearch`** (builds base and voltages together, for k too large to list the bases): BFS-canonical construction
  from a root, each vertex's remaining half-edges get a sorted multiset of targets, edges to new vertices carry
  voltage 0, the first nonzero voltage is 1; after each edge it records the NB walks through it (prefix · edge ·
  suffix) and prunes when some vertex has more than δ collisions. Collisions only grow as edges are added, so the
  pruning is exact.

Validation:
- `zplift` with pruning = `zplift -brute` (no pruning) on (p, D, k) = (7,5,4), (13,7,5), (11,7,5), (5,5,5), (3,5,4):
  8, 3,281, 38,903, 0, 336 normalized solutions both ways.
- `crosscheck.py` (independent: own DFS spanning tree, builds every lift, BFS diameter) = zplift × (p − 1) on
  (7,5,4), (3,5,4), (13,7,3) and (5,6,3) (even diameter): 48, 672, 38,688, 1,380.
- `jsearch` vs `zplift`, solution sets compared up to isomorphism of the lifted graphs (nauty `labelg`), simple cubic
  lifts: (p, k, D) = (7,4,5): 1 = 1 class; (3,4,5): 30 = 30; (13,3,7): 172 = 172; (13,5,7), 130-vertex graphs of
  diameter 7: 293 = 293 classes. (zplift also reports lifts with a double edge, which jsearch excludes; none occur in
  the D = 7 runs below.)
- Sharded `jsearch` runs reproduce the unsharded totals (13,5,7: 14,596 + 17,157 + 12,474 = 44,227 solutions).

### 3.2 Results for p ≥ 11 (Computer-checked)

Every prime p ≥ 11 and every k with 170 ≤ 2kp ≤ 248, all bases, D = 7. "searched" = bases that passed the base
filters; nodes = voltage-search nodes.

| p | k | n | bases | searched | nodes | solutions |
|---|---|---|---|---|---|---|
| 11 | 8 | 176 | 1,207 | 212 | 348,267 | 0 |
| 11 | 9 | 198 | 6,979 | 76 | 16,813 | 0 |
| 11 | 10 | 220 | 45,687 | 8 | 1,303 | 0 |
| 11 | 11 | 242 | 335,178 | 0 | 0 | 0 |
| 13 | 7 | 182 | 243 | 60 | 218,102 | 0 |
| 13 | 8 | 208 | 1,207 | 16 | 24,192 | 0 |
| 13 | 9 | 234 | 6,979 | 0 | 0 | 0 |
| 17 | 5 | 170 | 16 | 10 | 51,107 | 0 |
| 17 | 6 | 204 | 59 | 6 | 2,833 | 0 |
| 17 | 7 | 238 | 243 | 2 | 220 | 0 |
| 19 | 5, 6 | 190, 228 | 16, 59 | 7, 0 | 31,715, 0 | 0 |
| 23 | 4, 5 | 184, 230 | 6, 16 | 3, 1 | 11,506, 2,220 | 0 |
| 29 | 3, 4 | 174, 232 | 3, 6 | 3, 1 | 1,337, 592 | 0 |
| 31 | 3, 4 | 186, 248 | 3, 6 | 2, 0 | 955, 0 | 0 |
| 37, 41 | 3 | 222, 246 | 3 | 1, 0 | 44, 0 | 0 |
| 43, 47, 53, 59, 61 | 2 | 172–244 | 1 | 0 | 0 | 0 |
| 89, 97, 101, 103, 107, 109, 113 | 1 | 178–226 | 1 | 0 | 0 | 0 |

(Primes 67–83 have no admissible k; p ≥ 127 gives n ≥ 254.) Outputs: `research/d3D7exact/runs/zp_p*_k*.out`,
logs `run_small.log`, `run_mid.log`. Total time about 12 minutes on one core, most of it reading the 335,178 bases.

**Corollary (Computer-checked).** No bipartite graph with maximum degree 3 and diameter 7 on more than 168 vertices
has an automorphism of prime order p ≥ 11. This contains the earlier job's "no cyclic Haar graph" and "no 2+2, 3+3,
4+4 lift" results for cyclic groups of prime order and extends them to bases up to 11+11 (22 orbits).

### 3.3 Results for p = 7

| k | n | δ | Knuth estimate (nodes) | status |
|---|---|---|---|---|
| 13 | 182 | 36 | 1.6 × 10^8 | running (4 shards) |
| 14 | 196 | 29 | 7.5 × 10^9 | not run (too large) |
| 15 | 210 | 22 | 4.8 × 10^7 | running |
| 16 | 224 | 15 | 4.2 × 10^7 | running |
| 17 | 238 | 8 | 7.2 × 10^8 | running (8 shards) |

(To be filled in when the runs finish.)

## 4. Heuristic: what the exact searches cannot reach

Knuth random-probe estimates of the jsearch tree (validated: 2.0 × 10^3 vs 1,730 true, 4.2 × 10^3 vs 4,508,
8.0 × 10^3 vs 8,417, 1.0 × 10^7 vs 1.16 × 10^7 nodes on the test cases); at ~45,000 nodes per second per core:

| p | k | n | δ | estimated nodes |
|---|---|---|---|---|
| 5 | 22 | 220 | 17 | 1.6 × 10^9 |
| 5 | 23 | 230 | 12 | 1.0 × 10^12 |
| 5 | 24 | 240 | 7 | 3.1 × 10^11 |
| 7 | 14 | 196 | 29 | 7.5 × 10^9 |

The estimates have relative standard errors of 0.4–0.9 and heavy tails. jsearch has no isomorph rejection beyond
the BFS rule (every base is generated from each of its k side-0 roots and many child orders); real canonical
augmentation could cut this by orders of magnitude and would be the next step for order 5.

## 5. What is open, as mathematical questions

1. Is there a cubic bipartite graph of diameter 7 on 248 vertices? (§2.6 gives its forced local structure.)
   On 246, 244, 242 (δ = 4, 5, 6; girth ≥ 10)?
2. Does every cubic bipartite graph of diameter 7 with an automorphism of order 5 or 7 have at most 168 vertices?
   (Order 7: the cases left after §3.3; order 5: all n = 170..240 divisible by 10.)
3. Order 2 and 3 automorphisms can have fixed points, so the quotient is not a cover; no method here.
4. Graphs with trivial automorphism group are out of reach of everything above.

## 6. Files

- `research/d3D7exact/`: `zplift.c`, `jsearch.c`, `crosscheck.py`, `compare_iso.py`, `liftedges.py`, `bases/`,
  `runs/` (zplift outputs; `runs/js/` jsearch shards), README.md.
- Literature PDFs and the agent's scripts stayed in the session scratchpad (not committed).
