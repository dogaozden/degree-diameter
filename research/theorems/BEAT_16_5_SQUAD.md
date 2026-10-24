# Beating 31,460 at (16,5): squad run (job beat-16-5-squad)

Opus + Haiku squad, branch `claude/beat-16-5-squad-jiiwg2`, started 2026-10-24. Goal: a bipartite graph of maximum
degree 16 and diameter 5 on more than 31,460 vertices (the PG(4,3) flag graph; table value 27,300). The solo run
(job beat-16-5) writes BEAT_16_5.md; this file is the squad run's. Scripts and outputs: `research/theorems/squad165/`.
Squad rounds: `research/squads/LOG.md`.

Bounds used throughout: bipartite Moore bound 2(1 + 15 + 15² + 15³ + 15⁴) = 108,482, i.e. at most 54,241 vertices per
side (1 + 16·15 + 16·15³ same-side vertices within distance 4).

## Status (updated as the run goes)

No graph above 31,460 yet. Two new directions tested, both below the target, one with a working pipeline.

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

## 2. Bipartite route-chart lifts (Mizuno's construction made bipartite): works, tops out near 21,500

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

Why it is hard to push: the lift is K₄,₄-structured (each controller edge bundle is a union of K₄,₄'s, each vertex
in 4 of them), the same local structure as the flag graph. For K₄,₄-structured graphs of diameter 5 a counting bound
gives at most 33,145 vertices per side. The flag graph reaches 47.5 % of it; a controller lift needs m ≥ 62, i.e.
57 % of its own bound 108·256, while the best controllers found reach 39 %.

## Notes on what was ruled out before this run (theorem-search, REGULARITIES.md §1.2)

Voltage lifts of the flag graph (unique walks), affine versions (diameter 8), deletions down to degree 15.
