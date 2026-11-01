# Beating 31,460 at (16,5): squad run (job beat-16-5-squad)

Opus + Haiku squad, branch `claude/beat-16-5-squad-jiiwg2`, started 2026-10-24. Goal: a bipartite graph of maximum
degree 16 and diameter 5 on more than 31,460 vertices (the PG(4,3) flag graph; table value 27,300). The solo run
(job beat-16-5) writes BEAT_16_5.md; this file is the squad run's. Scripts and outputs: `research/theorems/squad165/`.
Squad rounds: `research/squads/LOG.md`.

Bounds used throughout: bipartite Moore bound 2(1 + 15 + 15² + 15³ + 15⁴) = 108,482, i.e. at most 54,241 vertices per
side (1 + 16·15 + 16·15³ same-side vertices within distance 4).

## Status (updated as the run goes)

**33,792 > 31,460, our own construction (06:33 UTC).** A bipartite graph of maximum degree 16 and diameter 5 on
**33,792** vertices: the route-chart lift (fibre F₄⁴, 16 = 4 letters × 4 scalars) of a 66 + 66 controller, the
voltage lift of K₃,₃ + perfect matching by Z₂₂. The chart has 8 singular nonbacktracking patterns and is
pencil-complete (§2.1). apsp.c: RESULT VALID d=16 D=5 n=33792; bfs_all.c: max eccentricity 5, all 33,792² ordered
pairs accounted for. Files: `graphs/build_d16D5_n33792.py` (self-contained builder with the explicit data),
`graphs/d16D5_n33792_k33m_z22.edges.gz`, check `graphs/d16D5_n33792_check.txt`. It also beats the 32,768 double
cover below. Details in §2.2.

Earlier: **32,768 > 31,460, but from someone else's graph.** The bipartite double cover G × K₂ of the (16,4) graph G on
16,384 vertices of Amarel, DeBardeleben, Grosskopf, Job, Lawrence, Monroe and Somasundaram (LANL; communicated to
the Comellas degree–diameter table on Sep 18, 2026, "graph-lift construction found using the agentic tool URSA")
is 16-regular, bipartite, on 32,768 vertices, with diameter exactly 5. Two independent all-pairs checks pass:
apsp.c (RESULT VALID d=16 D=5 n=32768) and a plain BFS from every vertex (`bfs_all.c`). From every vertex the
same-side vertices at distance 0, 2, 4 number 1 + 203 + 16,180 = 16,384, the whole side. Files:
`graphs/d16D5_n32768_doublecover_lanl_d16D4.edges.gz` (uncompressed sha256 20401e90…0f23d), builder
`squad165/double_cover.py`, check `squad165/runs/d16D5_n32768_check.txt`. The squad's literature card (r1 card 6)
found the lead: Wikipedia's general table lists N(16,4) ≥ 16,384 (note 28). Credit for G is theirs. Ours is only
the observation, the same kind of credit as the flag graph's 31,460. So by Doğa's rule this is probably not ours
either, and the run continues for a construction of our own.

## 1. Weyl-distance graphs of all finite buildings: only the flag graph (negative, complete)

The flag graph is one member of a family that can be enumerated without building any graph. Take a finite thick
building of type (W, S) with node parameters q_s; side A = residues of type I, side B = residues of type J (separate
copies); R ~ R' iff the Weyl distance δ(R, R') (a (W_I, W_J)-double coset) lies in a chosen union X of double cosets.
Then

- degrees d_A = N_X / P_J and d_B = N_X / P_I, with N_X = Σ_{x∈X} q_x and P_K = Σ_{v∈W_K} q_v;
- |A| = P_W / P_I, |B| = P_W / P_J;
- the Weyl distances reachable by walks follow from the BN-pair set product BxB·BsB = BxsB (l(xs) > l(x)), else
  BxB ∪ BxsB. So the exact diameter is a finite computation in W.

The flag graph of PG(4,3) is type A₄, q = 3, I = {2,4}, J = {1,3}, X = the identity double coset (selftest:
16-regular, 31,460, radii 4/5 on both sides). The table's 27,300 is not the G₂(4) chamber graph with X = {s₁s₂}
(13,650 vertices, diameter 8).

`weyl_graphs.py scan` runs over types A₂–A₆, B/C₂–₅ (also the twisted parameter patterns of ²D_{n+1}, ²A_{2n−1},
²A_{2n}), D₄, D₅, E₆, F₄ (also ²E₆), G₂ (also ³D₄), q up to 16 where degrees allow. It covers every pair of residue
types with both sides ≤ 54,241 and every union X with both degrees ≤ 16 (no truncation). Result
(`weyl_summary_out.txt`): **the only diameter-5 member above 15,000 vertices is the PG(4,3) flag graph.** Best others:

| building | sides | X | degrees | vertices | diameter |
|---|---|---|---|---|---|
| ²A₅(2) = PSU(6,2) | points / lines of H(5,4) | {e, s₃} | 15, 15 | 37,422 | 6 |
| ²D₄(2) = O⁻(8,2) | chambers / chambers | {s₁s₂, s₂s₁, s₃s₂} | 16, 16 | 32,130 | 6 |
| B₃(3)/C₃(3) | points / lines | {e, s₃} | 16, 16 | 29,120 | 6 |
| D₄(2) | chambers / chambers | {s₃s₂s₄, s₄s₂s₁} | 16, 16 | 85,050 | 7 |

Quotients do not rescue them (`balls.py` → `balls_out.txt`). In the D₄(2) chamber graph (85,050, diameter 7) a
same-side 4-ball holds 16,829 of 42,525 vertices, under the half that a free involution quotient (42,525 vertices)
would need. A Z₃ quotient would have only 28,350 vertices. Every other entry above is too small to halve.

## 2. Bipartite route-chart lifts (Mizuno's construction made bipartite): 33,792 (§2.2)

Mizuno (arXiv:2606.15860, June 2026) beat the *general* (16,5) record (147,456) with a "controller × route chart"
lift. A small 4-regular controller graph C, fiber F_q^n, and for a controller edge u→v labelled t: (u,x) ~
(v, A_t x + λ b_t), λ ∈ F_q. Degree 4q. A walk with an invertible "controllability matrix" reaches every point of the
target fiber.

Bipartite version (new as far as I know). C bipartite and 4-regular, q = 4, n = 4 (fiber of 256 points), so the lift
is 16-regular, bipartite, on 2·m·256 vertices (m = controller vertices per side). If every same-side ordered pair of
controller vertices (u = v included) is joined by a nonbacktracking walk of length exactly 4 with a nonsingular 4×4
matrix, every same-side pair of the lift is within distance 4, so the diameter is ≤ 5. m ≥ 62 would beat 31,460;
m ≤ 108 always (108 nonbacktracking walks of length 4 per vertex).

- **Chart:** for a Haar controller H(G, S) the walk i₁i₂i₃i₄ is nonsingular iff U(i₂;i₁) ⊕ U(i₃;i₄) = F₄⁴ with
  U(j;i) = A_j⁻¹⟨b_i, b_j⟩ (A side), and similarly with V(j;i) = ⟨b_j, A_jA_i⁻¹b_i⟩ (B side). `chart.py` found a
  **universal** chart (all 216 walk types nonsingular), `chart_u1.json`. So only the controller matters.
- **Haar controllers** (`ctrl_exh.c`, exhaustive over S ∋ e for a group given by its table; `meta_scan.py`): over all
  metacyclic groups of orders 40–108 the largest perfect controller is **m = 42** (Z₇ ⋊ Z₆, S = {0, 1, 7, 14}; also
  m = 40). Orders 43–57 and 63 stall at 2 uncovered elements (`meta_scan.log`).
- **General controllers** (`ctrl_anneal.c`, edge-switch annealing, 20 s): perfect at m = 40; 43, 193, 419 uncovered
  pairs at m = 48, 56, 62. Worse than Haar, as for Haar vs general graphs elsewhere.
- **Check:** `build_lift.py "meta 7 6 2" "0 1 7 14" chart_u1.json` → 21,504 vertices; apsp.c (all pairs, no
  symmetry): 16-regular, bipartite, diameter 5, RESULT VALID. Below the target, but it validates the pipeline.

- **More orbits help** (squad round 1 and `mlift.c`, which anneals the voltages of any base multigraph read from a
  file). A k-orbit controller is a voltage lift of a 4-regular bipartite base multigraph on k + k vertices by a
  group of order m/k. Largest perfect controllers found: k = 1 (Haar) m = 42; k = 2 m = 48 (Z₂₄, Z₆⋊Z₄); k = 3
  **m = 54** (K₃,₃ plus a doubled matching, Z₁₈; lift 27,648 vertices, apsp VALID d=16 D=5, checked twice). Floors
  at m ≥ 62: 2 (Haar, m = 63), 8 (k = 2, Z₃₁, exhaustive), 6 (k = 3, m = 63). About 500 group tables (metacyclic,
  non-metacyclic of order 62–108, non-split metacyclic) give no perfect Haar controller above m = 42.
- The lift is also not competitive in other cells: 3-regular controllers (degree 3q) are perfect only up to m = 12,
  giving 1,944 / 6,144 / 15,000 at (9,5) / (12,5) / (15,5) against 2,662 / 8,200 / 20,496.

### 2.1 The pencil lemma: distance-2 pairs for free

Exact-NB-4 is stronger than needed. Colour the controller properly with 4 colours, colour c using chart letter c.
For u ≠ v on the A side with a common neighbour a, let i, j be the colours of ua and va. Lifted walks of length 4
from (u, x) to the fiber of v that backtrack once (u→c→u→a→v, u→a→w→a→v, u→a→v→c→v) reach exactly the affine
3-spaces A_j⁻¹(A_i x + ⟨b_i, b_j, z⟩) for the 8 vectors z ∈ Z(i,j) = {A_iA_k⁻¹b_k : k≠i} ∪ {b_l : l∉{i,j}} ∪
{A_jA_k⁻¹b_k : k≠j}. They all contain the same 2-space, so **their union is the whole fiber iff Z(i,j) meets all five
hyperplanes through ⟨b_i, b_j⟩**. That is a condition on the chart alone; the B side is the same with
(A_c, b_c) → (A_c⁻¹, A_c⁻¹b_c). Call a chart *pencil-complete* if all 24 conditions hold.

**Theorem (route-chart lift, bipartite form).** Take a pencil-complete chart and a properly 4-edge-coloured 4-regular
bipartite controller C with m vertices per side. Suppose (i) C has bipartite diameter ≤ 5, (ii) every vertex lies on
a 4-cycle whose colour pattern is nonsingular for the chart, and (iii) every same-side pair at distance 4 is joined by
a nonbacktracking walk of length 4 with a nonsingular pattern. Then the lift is a 16-regular bipartite graph on 512m
vertices with diameter ≤ 5. (Same-side pairs: distance 4 by (iii), distance 2 by the lemma, distance 0 by (ii);
opposite-side pairs then within 5.) A diagonal pair needs a 4-cycle: closed walks that backtrack reach only planes
through x, at most 211 of the 256 fiber points.

Checks. `chart_search.c` finds pencil-complete charts quickly (`charts/chart_p4.txt`, `chart_p5.txt`; 12 of the 216
patterns singular), but a chart that is both pencil-complete and universal has not been found yet (best: 8
singular patterns, `charts/chart_u8.txt`, squad round 2). `lift_check.py` on the m = 50 relaxed Haar controller (Z₅⋊Z₁₀, S = {0,1,5,32}), which has
50 ordered pairs at distance 2 with **no** nonbacktracking walk of length 4: the lift reaches all of them. The only
misses are distance-4 pairs whose walks all have singular patterns, as predicted. `mlift_chart.c` anneals voltages of
a coloured base for exactly conditions (i)–(iii). Its m = 48 controller lifts to 24,576 vertices, apsp VALID d=16
D=5. At m = 63 (K₃,₃ + doubled matching, Z₂₁) the best controller has 2 uncovered pairs. Both are diagonals: one
orbit on each side has no 4-cycle. Everything else is covered.

Why exact-NB-4 controllers are hard to push: the lift is K₄,₄-structured (each controller edge bundle is a union of K₄,₄'s, each vertex
in 4 of them), the same local structure as the flag graph. For K₄,₄-structured graphs of diameter 5 a counting bound
gives at most 33,145 vertices per side. The flag graph reaches 47.5 % of it; a controller lift needs m ≥ 62, i.e.
57 % of its own bound 108·256, while the best controllers found reach 39 %.

### 2.2 33,792: K₃,₃ + perfect matching over Z₂₂ with an 8-singular chart

**Construction** (`graphs/build_d16D5_n33792.py` has all the data). Base: K₃,₃ with its perfect matching doubled
(a₀a₁a₂ | b₀b₁b₂, 12 edges). Controller: voltage lift by Z₂₂, (a_i, g) ~ (b_j, g + v_e), each controller edge carrying
its base edge's chart letter. Voltages and letters (edge: voltage/letter): a₀b₀ 0/0 and 15/2, a₀b₁ 0/1, a₀b₂ 0/3;
a₁b₁ 7/0 and 3/2, a₁b₀ 0/3, a₁b₂ 19/1; a₂b₂ 6/0 and 17/2, a₂b₀ 0/1, a₂b₁ 8/3. The matching digons use letters {0, 2},
the rest of K₃,₃ uses {1, 3}. Chart: `squad165/charts/chart_u8.txt` (A₀ = I; 8 of the 216 nonbacktracking patterns
singular, pencil-complete), found by squad round-2 card 5. Lift: 2·66·256 = 33,792 vertices, 16-regular, bipartite.

**Check.** apsp.c: RESULT VALID d=16 D=5 n=33792. bfs_all.c from every vertex: max eccentricity 5; ordered pairs at
distance 0..5 are 33,792 / 540,672 / 6,859,776 / 83,601,408 / 564,056,064 / 486,807,552, which sum to 33,792². The
self-contained script and the search pipeline give the same edge set. Check file `graphs/d16D5_n33792_check.txt`.

**How it was found.** At m = 63 and 66 the fixed-chart annealer kept failing on diagonals only, and forcing 4-cycles
(tying digon voltages by an involution, or forcing one trivial closed base walk per orbit) made it much worse. The
decisive test was a fake chart with every pattern nonsingular: K₃,₃ + matching over Z₂₂ then reaches cost 0 in
2,769 annealing steps. So the chart, not the controller, was the bottleneck. With round 2's new chart (8 singular
patterns instead of 12), 8 of the 24 colour relabellings reach cost 0 within 45 s (`mlift_chart.c`, one thread per run).

**Structure.** Every controller vertex lies on exactly one 4-cycle, so the 4-cycles partition the 132 vertices,
as in the LANL (16,4) controller. They come from two trivial closed base walks: the 4-cycle a₀b₀a₁b₁ through the
edges with voltages 15, 0, 7, 0 (15 + 7 ≡ 0 mod 22), and the a₂b₂ digon, whose voltage difference 11 is the
involution of Z₂₂. The controller uses 66 of the 121 same-side vertices a vertex can reach (1 + 12 + 108), 55 %.

**Next sizes.** m = 69 (Z₂₃) is at cost 2 and m = 72 (Z₂₄) at cost 6 on the same base (60 s runs). Squad round 3
is on m ≥ 67.

## 3. Other routes tested and dropped

| idea | test | result |
|---|---|---|
| quotients of the Lazebnik–Ustimenko graph D(4,16) (16-regular, 2·16⁴ vertices) | `lu_graphs.py`, `lu_ball.py` | last-coordinate quotients cover D(3,16), whose diameter is 6 (also q = 4, 5, 7, 8); a same-side 4-ball of D(4,16) holds 25,666 of 65,536, under half, so no involution quotient (65,536 vertices) can have diameter 5 |
| Singer-invariant surgery of the flag graph: add the 121 solids as a new orbit, rewire 16 edge orbits (31,581 vertices) | squad r1 card 8 | ≥ 77,844 pairs beyond distance 5; removing one edge orbit alone breaks 1,098 pairs per vertex |
| abelian Haar graphs | counting | same-side words s₁+s₂−s₃−s₄ give at most ≈ 18,700 elements for \|S\| = 16, so a cover above 15,730 would need a near-perfect order-4 difference basis; random S are far from it |

## Notes on what was ruled out before this run (theorem-search, REGULARITIES.md §1.2)

Voltage lifts of the flag graph (unique walks), affine versions (diameter 8), deletions down to degree 15.
