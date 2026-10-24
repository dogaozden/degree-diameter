# Chart lifts: the (16,5) route-chart lift as a family (job thm-chartlift)

Opus theorist sessions with Haiku squads, 2026-10-24. Round 1-2: branch `claude/chart-lift-family-wko52j`; round 3
(this update): branch `claude/chartlift-family-h3605i`. Scripts, charts, controllers and check outputs:
`research/theorems/chartlift/` (tool list in its README.md; round-3 tools and graphs in `chartlift/r3/`). Squad rounds:
`research/squads/LOG.md`, folders `research/squads/r1-chartlift/` and `r2-chartlift/`.

## Results first

New graphs. Each was rebuilt by a self-contained builder (stdlib only) and checked by two all-pairs programs:
apsp.c (the coordinator's checker; it also reports INVALID with D = 4, so the diameter is exactly 5) and bfs_all.c
(plain BFS from every vertex; the distance counts sum to n²).

| cell (Δ, D) | table | ours before | **new** | letters × field | controller (m per side) | chart | builder / check |
|---|---|---|---|---|---|---|---|
| (15, 5) | 20,496 | 20,736 | **25,272** | 5 × F₃ | Haar graph of Z₂₆ ⋊₃ Z₆ (156) | `r3/k5q3_pd112.txt` (112 singular, both diagonals) | `r3/graphs/build_d15D5_n25272.py`, `…_check.txt` |
| (12, 5) | 8,200 | 8,748 | **12,150** | 4 × F₃ | K₃,₃ + doubled matching over Z₂₅ (75) | `r3/k4q3_diag_s170.txt` (16 singular, both diagonals) | `r3/graphs/build_d12D5_n12150.py`, `…_check.txt` |
| (10, 5) | 4,000 | — | **4,032** | 5 × F₂ | Haar graph of Z₁₄ ⋊₉ Z₉ (126) | `charts/r2_k5_q2.txt` (230 singular, both diagonals) | `r3/graphs/build_d10D5_n4032.py`, `…_check.txt` |
| (8, 5) | 1,710 | — | 2,048 (round 2) | 4 × F₂ | K₄,₄ (Latin colouring) over Z₂ × Z₈ (64) | `charts/c4s2_k4_q2.txt` (48 singular) | `graphs/build_d8D5_n2048.py` |
| (16, 5) | 27,300 | — | 33,792 (beat-16-5 squad) | 4 × F₄ | K₃,₃ + doubled matching over Z₂₂ (66) | squad chart (8 singular) | branch `claude/beat-16-5-squad-jiiwg2` |

Z_M ⋊_t Z_N is the metacyclic group of pairs (x, y) with (x₁, y₁)(x₂, y₂) = (x₁ + t^{y₁} x₂ mod M, y₁ + y₂ mod N);
a Haar graph of a group G with connection set S = {s₀, …, s_{k−1}} joins a_g to b_{s g}, and the edge from s_c gets
letter c. The (10,5) controller came from squad round r2, card c4; the (12,5) voltages from round r3, card c2 (they
stalled at cost 2 with one chart class; scoring them against all 348 labelled singular sets of Proposition 12(c)
found a chart that works); both rebuilt and checked here; the (15,5) one is ours. Also found and checked: (12,5)
11,664 (K₃,₃ + doubled matching over Z₃ ⋊₂ Z₈, card r3-c2, and a 4+4 base over Z₃ × Z₆, card r3-c3) and 10,368
(Haar graph of Z₁₆ ⋊₃ Z₄, ours), (15,5) 22,680 (Haar graph of Z₃₅ ⋊₆ Z₄), (10,5) 4,032 again (Z₂₁ ⋊₄ Z₆, card r2-c5).

**What changed in round 3: charts that cover both diagonals.** A vertex's own fibre is reached by closed 4-walks.
Before, the charts at q = 3, 4 did not cover this "diagonal" with backtracking walks, so every controller vertex
needed a 4-cycle, and 4-cycles cap controllers hard (cubic: m ≤ 16, Theorem 8; 4-regular: m = 54–66 in practice).
Round 3 found charts at (k, q) = (4, 3) and (5, 3) that cover both diagonals and keep every pencil complete
(§3.1, Proposition 12). Then a controller only needs same-side distances ≤ 4 and a nonsingular nonbacktracking 4-walk
for each distance-4 pair (Theorem 11). Girth-6 controllers become usable, and plain Haar graphs of metacyclic groups
work at once: m jumps from 128 to 156 at (15,5) and from 54 to 64 at (12,5), where Haar graphs then stop
(Proposition 13) and small multi-orbit bases take over (m = 72, then 75).

**How the (4,3) chart was found (Lemma 5).** All the chart conditions at D = 5 (singular patterns, pencils, diagonals)
depend only on the points w_c and b_c and on the collineation that A_c induces from the lines through w_c to the lines
through b_c. Coordinates can be changed separately in the A-fibres and the B-fibres, so the points can be put in a normal
form, and the search is over 4 collineations of PG(2,3) (5,616 each). An exhaustive search (`r3/diag43/`) shows that a
(4,3) chart covers both diagonals only when w₀..w₃ and b₀..b₃ are both independent, and then it always has complete
pencils and exactly 16 singular patterns (the annealer used in rounds 1-2 never found any of these charts; its best
had 26 singular patterns and no diagonal). In particular **no perfect (4,3) chart exists**, and at (3,2) no chart covers
both diagonals at all.

**Main theorem (§3.1, Theorem 3; computer-assisted proof; round 2).** For every prime power q,

> **n_b(4q, 5) ≥ 108 q⁴.**

For q ≥ 3 this is the lift of one fixed 108-vertex controller, K₃,₃ + doubled matching over Z₁₈. Every same-side
pair of it, even a vertex with itself, is joined by a nonbacktracking 4-walk. The chart is any universal 4-letter
chart over F_q⁴, and such a chart exists for every prime power q ≥ 3. q = 2 is the 2,048 graph. The bound beats the
published table at every cell it touches: (8,5) 1,728 > 1,710, (12,5) 8,748 > 8,200, (16,5) 27,648 > 27,300. The
actual graphs do better at q = 2, 3, 4: 2,048 = 128·2⁴, 10,368 = 128·3⁴ and 33,792 = 132·4⁴. At q = 3, 4, 5 the lifts
of the fixed controller were also built and checked all-pairs: 8,748, 27,648 and 67,500 vertices (degree 20), apsp
VALID (`chartlift/runs/exact54_lifts.out`).

The cell-by-cell statements behind the table (§3.1, Theorems 2 and 11):

> **n_b(kq, 5) ≥ 2 m q⁴** whenever a k-regular bipartite controller with m vertices per side satisfies the chart
> conditions of Theorem 1 (with 4-cycles at every vertex), or of Theorem 11 (no 4-cycles, for a chart covering both
> diagonals). Explicitly: n_b(12,5) ≥ 2·64·3⁴, n_b(15,5) ≥ 2·156·3⁴, n_b(10,5) ≥ 2·126·2⁴, n_b(8,5) ≥ 2·64·2⁴,
> n_b(16,5) ≥ 2·66·4⁴.

The general product theorem n_b(kq, D) ≥ q^(D−1) · N(k, D) (Theorem 9) holds for every D once a "D-perfect" chart
exists, and it would give 15–25% records at D = 7 and 8. No perfect chart exists at D = 5 for the cells we need
((3,2) and (4,3) proved exhaustively, the rest by counting), and none was found at D = 7, 8 (§3.2).

**How the work was split.** Rounds 1-2: Opus built the tools, the theory and the first (12,5) record, and proved the
general theorems; two Haiku squads (14 cards) swept bases, groups and charts, and their (8,5) and (15,5) controllers
became records after independent rebuilds. Round 3: Opus found the diagonal idea, the star-collineation reduction, the
(4,3) and (5,3) charts and the (12,5) and (15,5) Haar controllers; squad round r2-chartlift (8 cards) found the (10,5)
controller and a (5,2) chart with 216 singular patterns, and mapped where Haar controllers stop (§3.3).

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

**Lemma 5 (what the chart conditions depend on; round 3).** Write σ_c for the collineation that A_c induces from the
star of lines through w_c (a PG(2,q)) to the star of lines through b_c = A_c w_c. Then
U(c;t) = σ_c⁻¹(the line b_c b_t) and V(c;t) = σ_c(the line w_c w_t).
So the singular patterns (Lemma 2), the pencils (Lemma 3: planes through b_i b_j spanned by V-lines and b-points, or
through w_i w_j spanned by U-lines and w-points) and both diagonals (Lemma 4: unions of the points, the lines w_s w_t or
b_s b_t, and the U- or V-lines) depend only on the points w_c, b_c and the collineations σ_c. Two further facts make
this usable. (i) Changing coordinates separately in the A-fibres and the B-fibres (A_c → Q A_c P⁻¹, b_c → Q b_c) gives
an isomorphic lift, so the labelled points (w_c) and (b_c) can each be moved to a fixed representative of their
PGL(4,q)-orbit. (ii) Every collineation between the two stars comes from some A_c with A_c w_c = b_c, and the remaining
freedom in A_c (maps fixing w_c and acting as a scalar on its star) changes none of the conditions. Proof: the
displayed formulas are the definitions of U and V read in the stars; the rest is Lemmas 2–4. ∎

Two tools follow. `r3/diag43/` searches the collineations exhaustively for small (k, q) (Proposition 12). And
`r3/chart_anneal3.c` (`MOVES=star`) anneals charts by left-multiplying A_c with transvections that fix b_c, which moves
σ_c and nothing else; it finds a (4,3) chart covering both diagonals in about 5 seconds, where the round-1/2 annealer
(random single entries of A_c) never found one in hours.

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
at Δ = 20, 30, outside the table. The Schwartz–Zippel step for k ≠ 4 is Theorem 14 (round 3); small-q charts for
k ≠ 4 were not searched.

**Theorem 14 (every k, large q; round 3).** For every k ≥ 3 and every prime power q > q₀(k) = 28k(k−1)³ + 4(k−1)
there is a universal k-letter chart over F_q⁴. Hence n_b(kq, 5) ≥ 2 m q⁴ for every exact k-regular bipartite
controller with m vertices per side, for all such q. With the controllers we have:

> n_b(3q, 5) ≥ 24 q⁴ (q > 680), n_b(5q, 5) ≥ 232 q⁴ (q > 8,976), n_b(6q, 5) ≥ 400 q⁴ (q > 21,020),
> and n_b(kq, 5) ≥ 2k q⁴ for every k ≥ 3 and q > q₀(k) (the controller K_{k,k}).

Proof. Fix A₀ = I. For a nonbacktracking pattern let P be its determinant polynomial (Theorem 3, part 2), of degree
≤ 16 (side A) or ≤ 12 (side B). A pattern uses at most 4 distinct letters; relabel them onto 0..3 keeping their order.
The relabelled pattern is a nonbacktracking 4-letter pattern, and P becomes its 4-letter polynomial after renaming
variables, and after setting A_l = I when letter 0 is not used (a specialisation, so it can only create zeros).
`integer_witness.py` showed that every 4-letter pattern polynomial is nonzero modulo every prime, so the same holds
for every k-letter pattern polynomial. The product F of all of them and of det A₁, …, det A_{k−1} is then nonzero modulo
every prime, and its degree is at most 2k(k−1)³·14 + 4(k−1) = q₀(k). By Schwartz–Zippel F has a non-root over F_q when
q > q₀(k), which is a universal chart. K_{k,k} is exact for every k ≥ 3: from a_i, the walk a_i b_x a_y b_z a_j with
y ∉ {i, j} and z ≠ x reaches every a_j ≠ a_i, and a 4-cycle returns to a_i. ∎
`r3/allk_family.py` → `r3/allk_family.out` checks the relabelling for k ≤ 8 (every k-letter pattern lands on one of
the 108 witnessed patterns per side), K_{k,k} for k = 3..8, and the exact controllers m = 12, 54, 116, 200 (cost 0).
None of these cells is in the table except through k = 4 (Theorem 3): the k = 3 family gives 24·3⁴ = 1,944 at (9,5),
below the table, and k = 5, 6 start at Δ = 20, 30.

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
- **Round 3 settles (4,3) completely: no perfect chart exists.** By Proposition 12(c) every (4,3) chart that covers
  both diagonals has exactly 16 singular patterns. (The annealer's "22 with diagonals" above was itself a miss: those
  charts did not cover the diagonals.)

**Theorem 11 (square-free controllers; round 3).** Suppose the chart has every pencil complete and covers both
diagonals. Then the lift of C has diameter ≤ 5 as soon as (i) C has same-side distances ≤ 4 and (ii) every same-side
pair at distance 4 is joined by a nonbacktracking 4-walk whose pattern is nonsingular. No 4-cycles are needed.
Proof: Theorem 1; distance-2 pairs are covered by pencils, and a vertex's own fibre by the backtracking walks. ∎
So n_b(kq, 5) ≥ 2 m q⁴ for every such C, and with a perfect chart n_b(kq, 5) ≥ q⁴ · N_b(k, 5), where N_b(k, 5) is the
largest k-regular bipartite graph of diameter ≤ 5 (Theorem 9 at D = 5). Instances, all built and checked all-pairs
with apsp (VALID at D = 5, INVALID at D = 4); the bold records and the 10,368 graph were also checked with bfs_all
(max eccentricity 5):

| (Δ, 5) | k × q | chart (singular patterns) | controller | m | lift | best (k,5) graph, m |
|---|---|---|---|---|---|---|
| (15, 5) | 5 × 3 | `r3/k5q3_pd112.txt` (112 of 640) | Haar, Z₂₆ ⋊₃ Z₆ | 156 | **25,272** | 177 (88%) |
| (15, 5) | 5 × 3 | same | Haar, Z₃₅ ⋊₆ Z₄ | 140 | 22,680 | |
| (12, 5) | 4 × 3 | `r3/k4q3_diag_s170.txt` (16 of 216) | K₃,₃ + doubled matching over Z₂₅ (voltages: squad r3-c2) | 75 | **12,150** | 81 (93%) |
| (12, 5) | 4 × 3 | `r3/k4q3_diag_cls1.txt` (16 of 216) | K₃,₃ + doubled matching over Z₃ ⋊₂ Z₈ (squad r3-c2) | 72 | 11,664 | |
| (12, 5) | 4 × 3 | same | 4+4 base over Z₃ × Z₆ (squad r3-c3) | 72 | 11,664 | |
| (12, 5) | 4 × 3 | `r3/k4q3_diag_tt.txt` (16 of 216) | Haar, Z₁₆ ⋊₃ Z₄ | 64 | 10,368 | |
| (12, 5) | 4 × 3 | same | Haar, Z₁₅ ⋊₂ Z₄ (t = 7, 11 also reach cost 0) | 60 | 9,720 | |
| (10, 5) | 5 × 2 | `charts/r2_k5_q2.txt` (230 of 640) | Haar, Z₁₄ ⋊₉ Z₉ (squad c4) | 126 | **4,032** | 177 (71%) |
| (10, 5) | 5 × 2 | squad c5 chart `r3/k5q2_c5_216.txt` (216 of 640) | Haar, Z₂₁ ⋊₄ Z₆ (squad c5) | 126 | 4,032 | |

The last column compares with the largest known (k,5) graph (162 vertices for k = 4, 354 for k = 5): a perfect
chart would allow the whole of it. The Haar controllers are found by `ctrl_search` in seconds to minutes; metacyclic
groups with a cyclic quotient of order 4 to 9 win, dicyclic and abelian groups do badly (§3.3).

**Proposition 12 (which charts can cover both diagonals; computer-assisted, round 3).**
(a) Counting (Proposition 6.3): both diagonals need k + C(k,2)(q−1) + k(k−1)q ≥ (q+1)(q²+1). For kq ≤ 16 this leaves
only (k, q) = (3,2), (4,2), (5,2), (6,2), (7,2), (8,2), (4,3), (5,3). It rules out (3,3), (3,4), (3,5) and (4,4), so
(9,5), the 3 × F₄ and 3 × F₅ splits, and (16,5) with 4 × F₄ keep needing 4-cycles everywhere. Remark: with F_q-subspace
steps of dimension d (fibre F_q^{4d}, degree k q^d) the count is the same with q replaced by q^d (in vectors), so
F₂-planes in F₂⁸ do not rescue (16,5) either (210 < 255 nonzero vectors covered).
(b) (3,2): **no chart covers both diagonals** (`r3/diag43/diag_k3q2.py`: every labelled configuration of three points
on each side, coincidences included, and all 168³ triples of collineations; one-sided coverings exist, 2,688 of them
for independent points). So (6,5) with 3 × F₂ always needs 4-cycles on one side.
(c) (4,3): **both diagonals can be covered only when w₀..w₃ and b₀..b₃ are both independent**, and then every such
chart has complete pencils and **exactly 16 singular patterns**, 8 on each side (`r3/diag43/diag_exhaust3.py`,
`diag_joint.c`, `diag_coinc.py`, `diag43_allsing.py`: 27 labelled configurations per side up to PGL(4,3), coincidences
included, 729 pairs; only the independent/independent pair has solutions: 72 in normal form, giving 1,152 distinct
charts once each letter's collineation is varied, all with 16 singular patterns, complete pencils and both diagonals;
outputs `diag_charts_all.out`, `diag_coinc.out`). As labelled sets (letters matter once a controller's edges are
coloured) there are exactly 348 different singular sets, each with 8 patterns per side; `all_flags43.py` writes all
of them with a chart realising each (`r3/flags43/s000..s347.{txt,flags}`). So for a fixed coloured controller one can
test every (4,3) chart that covers both diagonals at once; that is how the 12,150 graph was found.
(`classify_sing.py` gives 7 classes, but from one collineation per solution only.)
(d) (4,2): charts covering both diagonals with complete pencils have **at least 48 singular patterns**, and 48 is
attained (`charts/c4s2_k4_q2.txt`). `r3/dpmin/dp_min.c` scans all 168⁴ combinations of star collineations for each of
the 36 pairs of coincidence-free labelled configurations (pencils and singular counts are sums over pairs of letters,
so this is a few seconds per pair; `dp_min_k4q2.out`): the minimum is 48, reached by 12 pairs, all with w's and b's of
rank 3 (three collinear points); two tetrahedra need 72. (Coincident configurations were not scanned at q = 2.)
(e) (5,2), (5,3): such charts exist, with 216 and 92 singular patterns (`r3/k5q2_c5_216.txt` from squad r2 c5,
`r3/k5q3_pd_star23.txt` from `chart_anneal3 MOVES=star`); the minima are not known. (6,2) and (7,2): 602 of 1,500 and
1,314 of 3,024 (squad r2 c8, c7; one anneal each).

**Proposition 13 (Haar controllers stop at m = 64 at (12,5); computer).** For each of the 7 classes of (4,3) charts in
Proposition 12(c) and every group of order 65 to 81 that `r3/mkgroups.py` builds (88 groups: cyclic, Z_a × Z_b,
dihedral, dicyclic, metacyclic), no Haar graph satisfies Theorem 11: an exhaustive scan of all connection sets (one
element fixed to the identity; `r3/ctrl_exh.c`, the EXH mode written by squad card r2-c6; log `r3/exh_d12.log`) finds
minimum cost 2. Order 64 works (Z₁₆ ⋊₃ Z₄ and ⋊₅), so for Haar controllers m = 64 is the end. A Haar graph of order
82 to 121 would also be a 4-regular bipartite graph of diameter 5 on more than 162 vertices, a (4,5) record.
Controllers with 3 or 4 vertex orbits do go further: m = 72 (Theorem 11 table).

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
- Lift/Moore ratios: (12,5) 27%, (15,5) 25%, (8,5) 37%, (16,5) 31%. After round 3: (12,5) 10,368 / 32,210 = 32%,
  (15,5) 25,272 / 82,742 = 31%, (10,5) 4,032 / 14,762 = 27%.
- **Round 3: which Haar groups win.** With charts covering both diagonals, metacyclic groups Z_M ⋊_t Z_N with N = 4
  to 9 and a large cyclic normal part win at every cell: Z₂₆ ⋊₃ Z₆ and Z₃₅ ⋊₆ Z₄ at (15,5), Z₁₆ ⋊₃ Z₄ and Z₁₅ ⋊ Z₄ at
  (12,5), Z₁₄ ⋊₉ Z₉, Z₂₁ ⋊₄ Z₆ at (10,5) (and Z₂₈ ⋊₁₃ Z₄, Z₁₅ ⋊₇ Z₈ at m = 112, 120, squad-reported). Cyclic, abelian and dicyclic groups do badly (costs 20–118).
  Order-81 groups (odd order, no involutions) are also bad at (12,5) (cost ≥ 16).
- **The last uncovered target is often a central involution.** At (12,5) order 78 and at (15,5) order 160 the best
  Haar connection sets leave exactly one target per side uncovered, and it is a central element z of order 2. The
  proved part: in a Haar controller the walk a_x → … with letters (c₁, c₂, c₃, c₄) ends at h·x with
  h = s_{c₄}⁻¹ s_{c₃} s_{c₂}⁻¹ s_{c₁}, the reversed letters end at h⁻¹·x, and a pattern is singular exactly when its
  reverse is (Lemma 2: "U(i₂;i₁) meets U(i₃;i₄)" is symmetric; side B the same). So the uncovered targets are closed
  under inversion, and the walks reaching an involution z = z⁻¹ come in reversal pairs that are singular together (no
  nonbacktracking pattern is its own reverse, since i₂ ≠ i₃). An involution therefore has half as many independent
  chances, which fits it being the last hole. Groups of odd order avoid this, and at (15,5) the odd orders 165
  (Z₁₁ ⋊ Z₁₅, Z₃₃ ⋊ Z₅) reach cost 2 with side A fully covered, the two side-B holes being an inverse pair.
- **Controllers reach 71–88% of the best known (k, 5) graph** when the chart covers both diagonals: m = 156 of 177 at
  k = 5, q = 3 (92–112 singular of 640); m = 64 of 81 at k = 4, q = 3 (16 of 216); m = 126 of 177 at k = 5, q = 2
  (216–230 of 640). With 4-cycles required the old controllers were at 54/81 and 128/177.

### 3.4 Dead ends

- **D = 3 for Δ ≤ 16** (Proposition 5). The fibre is F_q², and a pair at distance 2 reached through the colour pair
  (c, c′) is covered only if b_c ≠ b_{c′} as points of PG(1,q); the diagonal needs all q + 1 points among the w's. So a
  regular controller with every colour pair good needs k = q + 1, i.e. Δ = q(q+1), and those cells have Moore graphs.
  (16,3) with 4 × F₄ fails the diagonal (k < q + 1). With 8 × F₂, three classes of letters force at least 7 bad pairs
  at each B-vertex, and a double count of the good pairs bounds the controller by 86 vertices, so the lift has at most
  344 < 396. (15,3) with 5 × F₃ would need the full 42-vertex PG(2,4) incidence graph (376/9 > 41). There every pair
  has a unique common neighbour, but two of the five b's coincide in PG(1,3), so bad pairs occur at every vertex.
- **k = 2** (Proposition 6.1) and **perfect D = 5 charts** (Proposition 7).
- **(6,5)**: k = 3, q = 2 needs m ≥ 22 (704 > 684). No (3,2) chart covers both diagonals (Proposition 12(b), proved),
  so one side always needs 4-cycles. Cubic controllers then stall at cost 7–8 for m = 22 (`runs/d6_*.out`).
- **(14,5) and (12,5) with many letters over F₂.** 7 × F₂ needs m ≥ 462 (the (7,5) record has m = 576); the only (7,2)
  chart covering both diagonals has 43% of its patterns singular, and Haar controllers stop at m = 300 (9,600 vertices,
  valid, below the table; squad r2-c7). 6 × F₂ at (12,5) now needs m ≥ 325; the (6,2) chart is 40% singular and Haar
  controllers reach cost 2 at m = 200 (squad r2-c8).
- **The record (4,5) graph as a (12,5) controller.** With a diagonal-covering (4,3) chart any 4-regular diameter-5
  graph is a candidate, so the 162-vertex (4,5) record graph (m = 81) would give 13,122. It is far off: over 6 proper
  colourings, all letter relabellings and chart classes 0, 1, 5 the best leaves 414 same-side pairs uncovered
  (`r3/gen_ctrl_cost.py`). Near-Moore graphs join most distance-4 pairs by a single walk, and 16 singular patterns of
  216 then miss about 3% of the pairs.
- **(8,5) beyond 2,048 with Haar controllers**: the (4,2) chart is optimal at 48 singular patterns (Proposition 12(d)),
  and an exhaustive scan over all 128 groups of order 60–81 finds no Haar controller (min cost 4); 2+2 bases reach
  cost 2 at m = 66 (squad r2-c6).
- **General (non-voltage) controllers** by colour-preserving switches (squad r1-c8): m = 44 at (8,5) and 36 at
  (12,5), far below voltage lifts. **Joint chart + voltage annealing** (r1-c7): cost 2 at m = 57, no gain.
- **D ≥ 7 with record controllers.** The record (3,8) and (5,8) graphs have no nonbacktracking 7-walk between adjacent
  vertices, because they have no 8-cycles through edges (`nbwalk_cover.py` → `runs/nbwalk_cover.out`). So a D = 8 chart
  would have to cover adjacent pairs with three detours, the hardest condition. Short cycles cannot replace it, as
  4-cycles did at D = 5.
- **(16,5) beyond 66 on K₃,₃ + matching**: even a hypothetical zero-singular chart leaves cost 2 at m = 69 and 72
  (`runs/k4univ/`). The limit is the controller's 4-cycles and diameter, not the chart.
