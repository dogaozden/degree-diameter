# Chart lifts: the (16,5) route-chart lift as a family (job thm-chartlift)

Opus theorist session with two Haiku squads, branch `claude/chart-lift-family-wko52j`, 2026-10-24. Scripts, charts,
controllers and check outputs: `research/theorems/chartlift/` (tool list in its README.md). Squad rounds:
`research/squads/LOG.md`, folders `research/squads/r1-chartlift/`, `r2-chartlift/`.

## Results first

New graphs. Each one was rebuilt by a self-contained builder (`chartlift/graphs/build_*.py`, stdlib only). Each was
then checked by two all-pairs programs: apsp.c (the coordinator's checker) and bfs_all.c (plain BFS from every vertex).

| cell (Δ, D) | table | lab before | **new** | letters × field | controller (m per side) | chart | check file |
|---|---|---|---|---|---|---|---|
| (12, 5) | 8,200 | — | **8,748** | 4 × F₃ | K₃,₃ + doubled matching over Z₁₈ (54) | `charts/r2_k4_q3.txt` (26 singular) | `graphs/d12D5_n8748_check.txt` |
| (15, 5) | 20,496 | — | **20,736** | 5 × F₃ | 5-regular 2+2 base over the dicyclic group of order 64 (128) | `charts/r2_k5_q3.txt` (112 singular) | `graphs/d15D5_n20736_check.txt` |
| (8, 5) | 1,710 | 1,764 | **2,048** | 4 × F₂ | K₄,₄ (Latin colouring) over Z₂ × Z₈ (64) | `charts/c4s2_k4_q2.txt` (48 singular) | `graphs/d8D5_n2048_check.txt` |

The (15,5) and (8,5) controllers came from squad round 1 (cards c6 and c4). I rebuilt and checked both. Cells
touched without a record: (9,5) 2,592 (beats the table's 2,496, not the lab's 2,662); (12,5) with 3 letters 8,192
(8 short of the table). (16,5) stays at the squad's 33,792.

**Main theorem (§3.1, Theorem 3; computer-assisted proof).** For every prime power q,

> **n_b(4q, 5) ≥ 108 q⁴.**

For q ≥ 3 this is the lift of one fixed 108-vertex controller, K₃,₃ + doubled matching over Z₁₈. Every same-side
pair of it, even a vertex with itself, is joined by a nonbacktracking 4-walk. The chart is any universal 4-letter
chart over F_q⁴, and such a chart exists for every prime power q ≥ 3. q = 2 is the 2,048 graph. The bound beats the
published table at every cell it touches: (8,5) 1,728 > 1,710, (12,5) 8,748 > 8,200, (16,5) 27,648 > 27,300. At q = 2
and q = 4 our graphs do better: 2,048 = 128·2⁴ and 33,792 = 132·4⁴. At q = 3, 4, 5 the lifts of the fixed controller
were also built and checked all-pairs: 8,748, 27,648 and 67,500 vertices (degree 20), apsp VALID
(`chartlift/runs/exact54_lifts.out`).

The cell-by-cell statements behind the table (§3.1, Theorem 2):

> **n_b(kq, 5) ≥ 2 m q⁴** whenever a k-regular bipartite controller with m vertices per side satisfies the chart
> conditions of Theorem 1. Explicitly: n_b(4q, 5) ≥ 108 q⁴ for q = 2, 3, 4 (one base graph, K₃,₃ + doubled matching
> over Z₁₈; for q = 3 and 4 even one and the same controller); n_b(3q, 5) ≥ 32 q⁴ for q = 3, 4 (one 32-vertex cubic
> controller, a Z₈-lift of the base [[1,2],[2,1]]); n_b(8,5) ≥ 2,048 = 2·64·2⁴; n_b(15,5) ≥ 20,736 = 2·128·3⁴; n_b(16,5) ≥ 33,792 = 2·66·4⁴.

The general product theorem n_b(kq, D) ≥ q^(D−1) · N(k, D) (Theorem 9) holds for every D once a "D-perfect" chart
exists, and it would give 15–25% records at D = 7 and 8. No D-perfect chart exists at D = 5 for the cells we need
(proved for (3,2), counting for the rest), and none was found at D = 7, 8 (§3.2).

**How the work was split.** Opus built the tools, the theory and the (12,5) record, and proved the general theorems.
Two Haiku squads (14 cards, `research/squads/LOG.md`) swept bases, groups and charts; their (8,5) and (15,5)
controllers became records after independent rebuilds here. Their negative results (no (4,4) chart below 8 singular
patterns, no gain from joint annealing or general switch annealing, exhaustive minima at Z₁₉) are listed below.

## 1. The construction

**Controller.** C is a bipartite graph with sides A and B, every vertex of degree k, with a proper edge colouring by
letters 0, …, k−1. Every regular bipartite graph has one (König).

**Chart.** For each letter c there is an invertible matrix A_c over F_q and a nonzero vector b_c ∈ F_q⁴. Write
w_c = A_c⁻¹ b_c.

**Lift.** The vertices are (u, x) with u ∈ V(C) and x ∈ F_q⁴. A controller edge u–v (u ∈ A, v ∈ B) of letter c
joins (u, x) to (v, A_c x + λ b_c) for every λ ∈ F_q. Each controller edge lifts to q³ copies of K_{q,q}, every
vertex has degree kq, and the order is |V(C)| q⁴. Colour edges are never doubled, so the lift is simple.

Controllers here are voltage lifts: a small base multigraph on r + r vertices, a group G, an element of G on each base
edge, and (a_i, x) ~ (b_j, v_e x). Then m = r|G|. Each controller edge keeps its base edge's letter.

## 2. Why it works: walks, patterns, pencils, the diagonal

All statements are for diameter 5, so the fibre has dimension 4 and the binding walks have length 4 (§3.1, Theorem 9
does general D).

**Lemma 1 (walk images).** A walk in C determines, for each start (u, x), the set of lifted endpoints. That set is
M x + S, built step by step: a step from side A along letter c maps (M, S) to (A_c M, A_c S + ⟨b_c⟩), a step from
side B maps it to (A_c⁻¹ M, A_c⁻¹ S + ⟨w_c⟩). Proof: one step reaches exactly the affine line A_c x + ⟨b_c⟩ (or
A_c⁻¹ y + ⟨w_c⟩), and images of affine sets add. ∎ So two lifted vertices on the same side are within distance 4 iff
the target lies in the union of the sets M x + S over all walks of length exactly 4 (shorter walks extend by
back-and-forth steps). The lift has diameter ≤ 5 iff all same-side pairs are within 4.

**Lemma 2 (singular patterns are meeting lines).** Let U(j;i) = A_j⁻¹⟨b_i, b_j⟩ and V(j;i) = A_j⟨w_i, w_j⟩. In
PG(3,q), U(j;i) is a line through w_j and V(j;i) is a line through b_j. For each j the lines U(j;·) form a "tripod"
(k−1 lines through w_j). A nonbacktracking 4-walk with letters (i₁, i₂, i₃, i₄) starting on side A has
S = A_{i₄}⁻¹A_{i₃}(U(i₂;i₁) + U(i₃;i₄)). So it reaches the whole target fibre iff the lines U(i₂;i₁) and U(i₃;i₄)
are skew. Side B is the same with the V-lines. Hence the number of singular patterns is twice the number of meeting
pairs of lines from different tripods. Checked against the direct computation on 10 charts:
`geometry_check.py` → `runs/geometry_check.out`, ALL AGREE.

**Lemma 3 (pencil).** Take u ≠ u′ on side A with a common neighbour v, with letters i on uv and j on vu′. The walks of
length 4 that use u–v–u′ plus one back-and-forth step at u, v or u′ all have M = A_j⁻¹A_i. Their S are A_j⁻¹ of the
3-spaces ⟨b_i, b_j, z⟩ with z ∈ {A_i w_t} ∪ {b_t} ∪ {A_j w_t}. In PG(3,q) these are the planes through the line
⟨b_i, b_j⟩ spanned by the V-lines V(i;t), V(j;t) and the points b_t. If they are all q + 1 planes through that line,
every target is reached. Call this the (i, j) pencil being complete. It can only hold if there are enough planes:
3k − 4 ≥ q + 1. Side B: the same in A-space, with the line ⟨w_i, w_j⟩, the U-lines and the points w_t. So the
side-A conditions on the U-lines and the side-B pencils live in the A-fibre, and vice versa. The only coupling between
the two spaces is that A_j maps w_j to b_j and its star of lines to the star at b_j.

**Lemma 4 (diagonal).** In a simple controller, the closed 4-walks at u are 4-cycles or backtracking. The backtracking
ones reach x + (the union of the lines ⟨w_s, w_t⟩ and U(s;t)) on side A, or ⟨b_s, b_t⟩ and V(s;t) on side B. So
either these lines cover PG(3,q), or u needs a 4-cycle whose letter pattern is nonsingular.

**Theorem 1 (criterion).** The lift has diameter ≤ 5 if C satisfies all of the following:
- C has same-side distances ≤ 4;
- every same-side pair at distance 4 is joined by a nonbacktracking 4-walk with a nonsingular pattern;
- every same-side pair at distance 2 has a common neighbour whose pencil is complete, or a nonsingular 4-walk;
- every vertex either has a nonsingular 4-cycle or its side's diagonal is covered.

`ctrl_search.c` counts the violations of these conditions over the voltage-group orbits; cost 0 means the lift has
diameter ≤ 5, and every record above was also checked on the lift itself.

**The 33,792 graph explained.** Its chart (squad round 2) has exactly two meeting U-pairs, U(0;2)~U(3;1) and
U(0;3)~U(1;0), and two meeting V-pairs, V(0;2)~V(1;2) and V(2;0)~V(3;1). Hence 8 singular patterns. All 24 pencils
are complete (5 planes needed, up to 8 available). The backtracking lines cover only 62 of the 85 points, so every
controller vertex needs a 4-cycle (`runs/structure_notes.out`). The controller has them by design: one base 4-cycle
with alternating voltage sum 0 and one doubled edge whose two voltages differ by the involution of Z₂₂. Each lifts
to disjoint 4-cycles through all its vertices. The remaining voltage freedom makes every distance-4 pair reachable
by a nonsingular walk. The new (12,5) controller has the same design: the digon a₀b₀ with voltages 0 and 9 (the
involution of Z₁₈) and the square a₁b₁a₂b₂ with 3 − 13 + 14 − 4 = 0. The same Z₁₈ voltages also satisfy the
(16,5) chart, so one controller gives both 8,748 and 27,648.

## 3. Ranked results

### 3.1 Proved

**Theorem 2 (the D = 5 family; computer-verified instances).** In each line below the chart and the voltages are
explicit (files in `chartlift/`). Each lift was built and checked all-pairs:

| (k, q) | Δ | controller | m | lift order | status vs best known |
|---|---|---|---|---|---|
| (4, 3) | 12 | K₃,₃ + doubled matching / Z₁₈ | 54 | **8,748** | record (table 8,200) |
| (4, 3) | 12 | same base / Z₁₇ | 51 | 8,262 | above table |
| (5, 3) | 15 | [[2,3],[3,2]] base / Dic₁₆ (order 64) | 128 | **20,736** | record (table 20,496) |
| (4, 2) | 8 | K₄,₄ Latin / Z₂ × Z₈ | 64 | **2,048** | record (lab 1,764) |
| (4, 2) | 8 | [[1,3],[3,1]] base / Z₃₀; K₄,₄ / Z₁₅; [[1,3],[3,1]] / Dic₇; K₃,₃+m / Z₁₈ | 60, 60, 56, 54 | 1,920, 1,920, 1,792, 1,728 | above lab / above table |
| (4, 4) | 16 | K₃,₃ + doubled matching / Z₂₂ (squad) | 66 | 33,792 | record (unchanged) |
| (4, 4) | 16 | the (12,5) controller / Z₁₈ | 54 | 27,648 | above table |
| (3, 3) | 9 | [[1,2],[2,1]] base / Z₈ | 16 | 2,592 | above table, below lab |
| (3, 4) | 12 | same controller | 16 | 8,192 | below table |

**Theorem 3 (universal charts for every q ≥ 3; the 108 q⁴ family).**
1. *Exact controller.* C₅₄ is K₃,₃ + doubled matching over Z₁₈, voltages in `chartlift/runs/exact54.volt`. Every
   same-side pair, including (u, u), is the pair of ends of a nonbacktracking 4-walk: `ctrl_search` with the flags
   `charts/nbonly_k4.flags` (no pencils, no diagonal) gives cost 0.
2. *Universal charts exist for every prime power q ≥ 3.* Fix A₀ = I; the other chart entries are 64 variables. By
   Lemma 2, side-A pattern (i₁,i₂,i₃,i₄) is nonsingular iff
   P = det[adj(A_{i₂})b_{i₁}, adj(A_{i₂})b_{i₂}, adj(A_{i₃})b_{i₃}, adj(A_{i₃})b_{i₄}] ≠ 0, a polynomial of degree ≤ 16.
   Side B uses det[A_{i₂}adj(A_{i₁})b_{i₁}, b_{i₂}, b_{i₃}, A_{i₃}adj(A_{i₄})b_{i₄}], degree ≤ 12. Multiply the 216
   pattern polynomials and det A₁·det A₂·det A₃; the product F has degree ≤ 3,036. `integer_witness.py` finds 223
   integer charts at which, for every pattern, the values have gcd 1. So every factor, hence F, is nonzero modulo
   every prime (`runs/integer_witness.out`). By Schwartz–Zippel, F has a non-root over F_q whenever q > 3,036, which
   is a universal chart. For 3 ≤ q ≤ 3,036, all 469 prime powers, an explicit universal chart is in
   `charts/universal/k4_q<q>.txt`, found by `chart_anneal.c` (q ≤ 127) or random search (`universal_large.py`).
   Every chart was rechecked from the walk rules of Lemma 1 (q ≤ 127 in a second, Python implementation). Field
   convention: gf.py's polynomial for q ∈ {4, 8, 9, 16, 25, 27, 32, 49}, otherwise the first monic irreducible.
3. *Conclusion.* Universal means every nonbacktracking 4-walk reaches the whole target fibre (Lemma 2). So the lift
   of C₅₄ has diameter ≤ 5 for every q ≥ 3: n_b(4q, 5) ≥ 2·54·q⁴ = 108 q⁴. ∎
   q = 2 has no universal chart (Proposition 6.4), but the (8,5) graph gives 2,048 ≥ 1,728.

**Remark 4 (the same shape for other k).** The argument works for any k:

> n_b(kq, 5) ≥ 2 m_k q⁴

whenever C has m_k vertices per side, is k-regular and exact, and a universal k-letter chart over F_q⁴ exists. The
base K_{k−1,k−1} + doubled perfect matching gives exact controllers for every k we tried (`ctrl_search` with
`charts/nbonly_k*.flags`, `runs/exact*_z*.volt`): m₃ = 12 (Z₆), m₄ = 54 (Z₁₈), m₅ = 116 (Z₂₉) and m₆ ≥ 200 (Z₄₀). For
comparison, m_k ≤ k(k−1)³ = 24, 108, 320, 750, since there are that many nonbacktracking 4-walks from a vertex.
Universal charts need k((k−1)q+1) ≤ (q+1)(q²+1) when the b's are in general position, so for k = 5, 6 the family starts
at Δ = 20, 30, outside the table. The Schwartz–Zippel step for k ≠ 4 was not carried out; it would need its own
witnesses and small-q charts.

**Proposition 5 (ceiling).** A chart lift for (Δ, D) = (kq, D) has fibre dimension D − 1, and its controller is
k-regular with diameter ≤ D. So its order is at most q^(D−1) · Moore_b(k, D), and realistically
q^(D−1) · n_b(k, D). `reach_table.py` → `runs/reach_table.out` lists every cell with Δ ≤ 16 and 3 ≤ D ≤ 10. At D = 3,
4, 6 only four cells pass the Moore ceiling: (15,3) by 0.5%, (16,3) by 5–15%, (16,4) by 18% and (16,6) by 33%. The two
D = 3 cells are ruled out by the chart conditions themselves (§3.4). (16,4) and (16,6) would need 8 letters over F₂ and
a controller with 85% of the vertices of the GQ(7,7) incidence graph, or 75% of GH(7,7)'s; these two long shots were
not pursued. At D = 5 every cell with a factorisation Δ = kq, k ≥ 3, can be reached in principle. At D ≥ 7 a cell
needs a controller at 80–99% of the best known (k, D) graph; see Theorem 9.

**Proposition 6 (limits on charts).**
1. k = 2 is useless at D = 5: a 2-regular controller is a cycle. The pencil needs 3k − 4 = 2 ≥ q + 1, which fails.
   The only working controller is a doubled edge, giving 2q⁴ vertices.
2. Pencils can be complete only when q ≤ 3k − 5 (Lemma 3). So for k = 3 the pencil lemma works up to q = 4, and for
   (k, q) = (3, 5) every distance-2 pair needs a nonsingular 4-walk.
3. Diagonal by backtracking (Lemma 4) needs k + C(k,2)(q−1) + k(k−1)q ≥ (q+1)(q²+1) (count of covered points). This
   fails for (3,3), (3,4), (4,4). For those, every controller vertex needs a 4-cycle.
4. Universality with the b's in general position (no three collinear) needs the k tripods to be disjoint:
   k((k−1)q + 1) ≤ (q+1)(q²+1). This is impossible for k > q + 1 and tight for k = q + 1.

**Proposition 7 (no perfect chart at (3,2); (4,3) in general position).** Call a D = 5 chart perfect if it is
universal (no singular pattern), all pencils are complete and both diagonals are covered. A perfect chart would turn
every k-regular diameter-5 graph into a controller: the 56-vertex (3,5) graph would give 896 at (6,5), and the
162-vertex (4,5) graph 13,122 at (12,5).
- **For (k, q) = (3, 2) no perfect chart exists.** Proof. The A-diagonal needs the b's non-collinear, because collinear
  b's leave at most 12 of the 15 points covered. Then A-universality makes the three 2-pods disjoint; they have
  5 + 5 + 5 = 15 points, so they partition PG(3,2). 2-pods are planar. If q + 1 planes cover PG(3,q), they are the
  pencil of planes through one line L (dual Bose–Burton). Counting the points of L then forces every pod's missing
  line to be L, and every apex w_j to lie on L. But then each side-B pencil sees only the two planes π_i and π_j, while
  it needs 3. ∎
- **For (4, 3), the same holds when the b's are in general position.** Universality again forces a partition of
  PG(3,3) into 4 tripods. An exact cover search (`tripod_cover.py`, `runs/tripod_cover.out`) finds 3,120 such
  partitions, all planar, so the same argument applies: the w's are collinear and the B-pencils fail. With three
  collinear b's the counting is not decisive. There the annealer never got below 22 singular patterns with pencils
  and diagonals required.

**Theorem 8 (cubic controllers stop at m = 16; so k = 3 gives at most 32 q⁴).** Let C be cubic and bipartite,
with same-side distances ≤ 4 and every vertex on a 4-cycle. Then C has at most 16 vertices per side. This is exactly
what a 3-letter chart lift at D = 5 needs for q ≥ 3, because the backtracking walks cannot cover the diagonal there
(Proposition 6.3). So for q ≥ 3 every 3-letter chart lift of diameter 5 has at most 32 q⁴ vertices. The bound is
attained for q = 3, 4 (2,592 and 8,192).
Proof. Look from a vertex u. Suppose first that u lies on two 4-cycles. Then |N₂(u)| ≤ 4 and |N₃| ≤ 3|N₂| − 6 ≤ 6,
so m ≤ 1 + 4 + 12 = 17. Equality needs every level to be tree-like. But some vertex near u must lie on its own 4-cycle:
b′ when the two cycles share one edge, the third neighbour c when they share two. That cycle always creates a
coincidence at level 2, 3 or 4, so m ≤ 16. Suppose instead that every vertex lies on exactly one 4-cycle. Then the
4-cycles are disjoint and partition the vertices into "squares", so m is even. Write x₃ and x₄ for the coincidences at
levels 3 and 4; then m ≤ 24 − 3x₃ − x₄. The square of u's third neighbour gives x₃ ≥ 1, and the squares of a′ and b′
give x₄ ≥ 2, so m ≤ 19 and m ∈ {16, 18}.
For m = 18 (9 squares): the two A-vertices of a square are interchangeable, and so are its two B-vertices. So the
graph is determined by the 2-in-2-out digraph of external edges between squares. That digraph is the union of two
derangements P₁, P₂ (König), and relabelling the squares turns P₁ into a fixed representative of its cycle type.
`square_exhaust.c` tests every cycle type with every P₂: 1,067,968 graphs, none with all same-side distances ≤ 4
(`runs/square_exhaust_s9.out`). The same program finds 5 valid graphs at 8 squares, as a sanity check. ∎
The m = 16 examples are Z₈, D₄ or Q₈ lifts of [[1,2],[2,1]].

**Theorem 9 (product theorem; proved, not yet instantiated).** View the controller's universal cover as the k-regular
tree, i.e. the Cayley graph of Z₂ * ⋯ * Z₂ (k copies). A walk is a word in the letters and its end is the reduced
word. Call a chart over F_q^(D−1) **D-perfect** if, for both start sides and every reduced word y with
|y| ≤ D − 1, |y| ≡ D − 1 (mod 2), the words of length D − 1 that reduce to y have spans covering F_q^(D−1). (All those
walks share the linear part M, because a cancelled pair contributes A_c⁻¹A_c = I.) Then for every k-regular bipartite
graph C of diameter ≤ D the lift has diameter ≤ D, so

  **n_b(kq, D) ≥ q^(D−1) · N_reg(k, D)**, where N_reg is the largest k-regular bipartite graph of diameter ≤ D.

Proof: in C, following a word from u ends where following its reduced word ends (a letter followed by itself returns
along the same edge). So the walks from u to u′ include all words reducing to the colour word of a geodesic. ∎
At D = 5 this is exactly "perfect" (universal + pencils + diagonals). `perfect2.c` (F₂, bitmasks) and `perfectq.c`
(any F_q, coverage computed modulo the path span) compute the deficiency. They agree with an independent slow
implementation (`tree_perfect.py`) on every test chart (D = 5, 6, 7; q = 2, 3). What a D-perfect chart would give, with
controllers we have: (9,8) 2187 × 288 = 629,856 (lab 540,360); (15,8) 78,125 × 288 = 22.5M (lab 18.1M); (6,8)
128 × 288 = 36,864 (lab 31,680); (10,8) 128 × 9,576 = 1,225,728 (table 1,176,480). The 288-vertex cubic (3,8) graph
and the 9,576-vertex 5-regular (5,8) graph are rebuilt in `chartlift/controllers/` (apsp VALID).

### 3.2 Conjectured with strong evidence

- **8 singular patterns is the minimum for a pencil-complete (4,4) chart.** Squad card r1-c5 tested all 12,850 one-
  and two-entry neighbours of the squad chart (58 stay pencil-complete, none has fewer than 8), plus symmetric ansatzes.
- **At D ≥ 7 over F₂ no chart is D-perfect.** The deficiency is almost entirely at the top distance (universality):
  D = 7: 1,920 of 2,038 missing pairs at |y| = 6; D = 8: 10,048 of 10,180 at |y| = 7. A random pair of 3-flats in F₂⁶
  is complementary only 37% of the time, against 58% over F₃ and 69% over F₄.
- **Over F₃ the short distances block instead.** 3-letter searches over F₃⁶ (D = 7) and F₃⁷ (D = 8) with `perfectq.c`
  (20 minutes each) end with deficiencies of 14,872 and 122,292 target-vectors. At D = 7 side B became fully
  universal, but the diagonal and the |y| = 2 and 4 targets stay open. Each needs many nearly disjoint subspaces,
  e.g. ≥ 28 planes of PG(5,3) from at most 87 closed words. This is the same trade-off as at D = 5: universality wants
  q large, short-distance coverage wants q small.

### 3.3 Weak patterns

- **Which bases win.** When the chart does not cover the diagonal (q = 3, 4), winning controllers carry built-in
  4-cycles: one digon with an involution plus one zero-sum square on K₃,₃ + doubled matching. When the chart covers it
  (q = 2), K₄,₄ with a Latin-square colouring beats everything (m = 64 against 54). Pinning K₄,₄ voltages to create
  4-cycles makes it much worse (cost 58–85 at m = 68–72).
- **Non-abelian groups at the frontier:** dicyclic groups (orders 28 and 64) give the (8,5) m = 56 and (15,5)
  m = 128 controllers.
- **Fewer singular patterns help less than expected.** (4,3) charts with 24 singular patterns do no better than 26
  at m = 57 (cost 2 either way, squad r1-c3). The limit there is the controller.
- Lift/Moore ratios: (12,5) 27%, (15,5) 25%, (8,5) 37%, (16,5) 31%.

### 3.4 Dead ends

- **D = 3 for Δ ≤ 16** (Proposition 5). The fibre is F_q², and a pair at distance 2 reached through the colour pair
  (c, c′) is covered only if b_c ≠ b_{c′} as points of PG(1,q); the diagonal needs all q + 1 points among the w's. So a
  regular controller with every colour pair good needs k = q + 1, i.e. Δ = q(q+1), and those cells have Moore graphs.
  (16,3) with 4 × F₄ fails the diagonal (k < q + 1). With 8 × F₂, three classes of letters force at least 7 bad pairs
  at each B-vertex, and a double count of the good pairs bounds the controller by 86 vertices, so the lift has at most
  344 < 396. (15,3) with 5 × F₃ would need the full 42-vertex PG(2,4) incidence graph (376/9 > 41). There every pair
  has a unique common neighbour, but two of the five b's coincide in PG(1,3), so bad pairs occur at every vertex.
- **k = 2** (Proposition 6.1) and **perfect D = 5 charts** (Proposition 7).
- **(6,5)**: k = 3, q = 2 needs m ≥ 22 (704 > 684). The best (3,2) chart with complete pencils misses one diagonal
  vector on one side (8 singular patterns, `charts/r3_k3_q2_s41.txt`), so that side still needs 4-cycles. Cubic
  controllers then stall at cost 7–8 for m = 22 (`runs/d6_*.out`). **(14,5)**: 7 × F₂ needs m ≥ 462 of at most 576 with a non-universal chart.
- **General (non-voltage) controllers** by colour-preserving switches (squad r1-c8): m = 44 at (8,5) and 36 at
  (12,5), far below voltage lifts. **Joint chart + voltage annealing** (r1-c7): cost 2 at m = 57, no gain.
- **D ≥ 7 with record controllers.** The record (3,8) and (5,8) graphs have no nonbacktracking 7-walk between adjacent
  vertices, because they have no 8-cycles through edges (`nbwalk_cover.py` → `runs/nbwalk_cover.out`). So a D = 8 chart
  would have to cover adjacent pairs with three detours, the hardest condition. Short cycles cannot replace it, as
  4-cycles did at D = 5.
- **(16,5) beyond 66 on K₃,₃ + matching**: even a hypothetical zero-singular chart leaves cost 2 at m = 69 and 72
  (`runs/k4univ/`). The limit is the controller's 4-cycles and diameter, not the chart.
