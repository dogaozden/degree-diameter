# STATUS: omega45 (q = 7, Theorem 4.5 of research/theorems/OMEGA_REPAIR.md)

**Verdict: partial.** Lemma 4.2 and an exact Lemma 3.1 are formalised without hypotheses, and Theorem 4.5 is
formalised as a reduction: the final double count of the note is proved in Lean, from two statements about the
hexagon that stand for Lemma 4.3 (computer-checked in the note) and Lemma 4.4 (character-sum bound). Those two
statements are **not** proved here. Everything builds, with no sorry, admit or native_decide; `Axioms.out.txt`
shows only `propext`, `Classical.choice`, `Quot.sound`. All new files are under
`lean/BipartiteDD/LeanMaxx/Omega45/`. The branch also carries `LeanMaxx/Omega2`, `Omega3`, `Projection` and the
STATUS files copied unchanged from claude/thm-omega3-formalization-r197t8 (the build needs them). That branch
has no `research/lean-maxx/VERIFY-omega3.md`; I used its `STATUS-omega3.md`.

## What is proved

| item | Lean | status |
|---|---|---|
| Lemma 3.1, exact constant: `|{x ∈ opp t : dist z x ≤ 4}| ≤ q⁴` for a centre `z` of the colour of `t`, any generalized hexagon of order `(q,q)` | `Exact.lean`: `card_ballOpp_four_le_exact` | **proved** (Omega3 only had `q⁴ + 2q²`; the exact value is needed because the margin at q = 7 is 98..343 vertices) |
| `|F0| = α` and `|D2| ≤ 140` for the missed copy of Lemma 3.2, q = 7, every block pattern, α ≤ 5 | `Tab7.lean`: `star7` | **proved** by `decide +kernel` (32 patterns at α = 5, split into 32 kernel evaluations; ~7 min, ~7 GB) |
| Far pair from a bound on the radius-4 part of the cover | `Cover.lean`: `far_of_rad4`, `far_of_centres` | **proved** (the argument of `omega3_far`, with `covSet ⊆ rad4 ∪ rad2` and radius-2 balls counted as distinct words) |
| **Lemma 4.2** (coincidences: if two of `t, y₁(t), …, y₅(t)` coincide at some row of the unbarred colour, ΩH₇ has a far pair; ≥ 343 far vertices in the note) | `Q7.lean`: `omega45_lemma42` | **proved**, any hexagon of order (7,7), any pattern, any twisted labelling |
| q = 7 with **α ≤ 4 blocks**: every twisted / geometric labelling has diameter ≥ 9 | `omega45_alpha_le_four`, `omega45_geometric_alpha_le_four`, `Concrete7.lean`: `omega45_hexagon_alpha_le_four`, `…_geometric_…`, `…_geometric_shared_…` (at `H(F)`, `|F| = 7`) | **proved, unconditional** (not Gómez's wiring, which has α = 5; with α ≤ 4 there are at most four radius-4 centres, so Lemma 4.2 applies at every row) |
| **Theorem 4.5 as a reduction** (α = 5, both readings) | `Q7.lean`: `omega45_of_hyps`; `Geometric7.lean`: `omega45_geometric_of_hyps`; `Dual7.lean`: `omega45_geometric_of_hyps_points` | **proved modulo `PerpBound` and `Bonferroni`** (below) |

`Dual7.lean` + `Flip.lean` give the dual reading: exchanging the two hub bars, the block types a ↔ b, rotating
the positions of a type-b block by −1 and shifting barred class indices by −1 is a graph homomorphism onto the
flipped wiring (`metPos_flip`, a finite check; the identity was also checked in Python). So the hypotheses
are only needed for the colour class `p` of the points, for either reading.

## The two statements that are not proved (hypotheses of `omega45_of_hyps`)

Both are statements about the incidence graph `B` of the hexagon and a colour class `ε` (the points), in
`Q7.lean`:

* `PerpBound B κ ε 4144` (**Lemma 4.4**): every colour-preserving automorphism `h` of `B` with no fixed point of
  colour `ε` has `|{s : κ s = ε, dist s (h s) ≤ 4}| ≤ 4144`.
* `Bonferroni B κ ε 4 140` (**Lemma 4.3**): for `t` and five other points `Y` of colour `ε`, if fewer than 4
  of the 15 pairs of `{t} ∪ Y` are at distance ≤ 4, then `|⋃_{y∈Y} {x : dist t x = 6, dist y x ≤ 4}| + 140·49 <
  7⁵`. The note proves the same with "fewer than 6"; `bonferroni_mono` gives 6 ⇒ 4, and 4 already suffices
  for the double count (`4 · 16807 > 15 · 4144`, the note's remark).

What `omega45_of_hyps` does prove (the rest of Theorem 4.5): with `hno` (no far pair) Lemma 4.2 forces five
distinct centres different from `t` at every row of colour `ε` (so `α = 5`, `g_c = λ_{c'} λ_c⁻¹` has no fixed
row, and `g_c⁻¹ g_e` none for `c ≠ e`); `Bonferroni` then gives ≥ 4 close pairs at every row; summing over the
≥ q⁵ rows and swapping the sums gives `4 · 16807 ≤ (10 + 20) · 4144`, false. Distances are preserved by
automorphisms (`dist_aut`). This part is a faithful transcription of the proof of Theorem 4.5.

## What is missing, and why it is not a small step

* **Lemma 4.4.** Needs (a) the bridge "hexagon distance ≤ 4 between points ⟺ polar perpendicularity" for the
  concrete `H(7)` (the repo has the easy direction through `Hexagon/Plane.lean`; the hard direction needs
  `|x^⊥ ∩ Q(6,q)| = q⁴+q³+q²+q+1` at an arbitrary singular point), (b) that every collineation of `H(7)` is a
  linear map in `G₂(7) ≤ SO(7,7)` (classification, not in Mathlib), (c) the Gauss-sum count
  `#{Q = F = 0} = q⁻² Σ ψ(aQ + bF)` with ranks via diagonalisation, (d) the eigenvalue structure of `G₂` on the
  7-dimensional module (a multiplicity ≤ 3 and 3 only if μ³ = 1), which is where `3 | q − 1` enters, (e) the
  Schur-convexity step. An exhaustive count over `G₂(7)` (order 6.6·10¹¹) is not feasible even up to conjugacy
  without a proved class list.
* **Lemma 4.3.** Needs Lemma 4.1 (overlaps `≥ q³ − q`, triples `≤ (q+1)²`: point counts of quadrics in
  `⟨y,y′,t⟩^⊥`, with rank and type of the Gram matrix; no Witt theorem in Mathlib) and the 17-type analysis
  of the note (`degen.py`), which lives in `PG(6,7)`. Lemma 4.1 is **not** formalised. No abstract (distance
  only) argument can replace it: for three mutually opposite points the overlap is `q³ − q` or `q³ + q`
  according to the discriminant of the plane, which the incidence graph does not see.
* The reading with mixed inner classes of reading 1 (not in the note's q = 7 case) and non-geometric
  labellings are not covered (as in omega3).

## Differences from the note (all harmless)

1. Lemma 4.2: the note says at least `q⁵ − 4q⁴ − 140·49 = 343` far vertices. Lean proves the existence
   (`16807 > 4·2401 + 140·49 = 16464`).
2. The radius-2 count is `|D2|`, the number of distinct words `λ_a λ_b⁻¹` other than the identity and the
   radius-4 centres. Python (an independent re-implementation of `Wiring.lean`; same F0, F1, F2, F3 definitions)
   gives the maximum `4, 23, 52, 91, 140` over all patterns for α = 1…5 (the index count `m2` of Omega3 is
   5, 25, 55, 95, 145). 140 is the note's `m₂ ≤ 140`, and `star7` confirms it in the kernel.
3. `Bonferroni` is stated for `k = 4` (see above); `|F0| = α = 5` and the starved pair is the Lean `cstar` for the
   unbarred class 0 (the note's "starved pair" with unbarred X); the barred case is obtained by the flip.

## Build and check (reproduce)

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Omega45.Dual7 BipartiteDD.LeanMaxx.Omega45.Concrete7   # Tab7 ~7 min, ~7 GB
    lake env lean BipartiteDD/LeanMaxx/Omega45/Axioms.lean

`grep -nE "sorry|admit|native_decide|implemented_by|unsafe" lean/BipartiteDD/LeanMaxx/Omega45/*.lean` has no
hits. Memory: `Tab7.lean` first ran out of memory (exit 137) as one `decide +kernel` over all 32 patterns; it is
now 32 separate kernel evaluations glued by `tab7_5_all`.

## Files

| file | content |
|---|---|
| `Exact.lean` | exact Lemma 3.1 (`X2_ge_four/six`, `T3_le_four/six`, `card_ballOpp_four_le_exact`) |
| `Cover.lean` | `rad4`, `cen4`, `D2`, `rad2`, `covSet_subset`, `far_of_rad4`, `far_of_centres` |
| `Tab7.lean` | `star7`: `|F0| = α`, `|D2| ≤ 140` at q = 7 (kernel) |
| `Q7.lean` | `omega45_lemma42`, `omega45_alpha_le_four`, `PerpSet/PerpBound/Bonferroni`, `omega45_of_hyps`, `dist_aut` |
| `Flip.lean` | exchange of the hub bars: `metPos_flip`, `flipV`, `flipV_adj`, `flipV_surj`, `exists_far_of_hom` |
| `Geometric7.lean` | `geometric_far_of_nf` and the geometric-labelling forms |
| `Dual7.lean` | both readings: `omega45_geometric_of_hyps_points` |
| `Concrete7.lean` | `H(F)`, `|F| = 7`, α ≤ 4, unconditional |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` of the headline theorems |
