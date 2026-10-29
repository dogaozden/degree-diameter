# STATUS: omega45b (q = 7, Theorem 4.5 of research/theorems/OMEGA_REPAIR.md, concrete H(7))

**Verdict: partial, one classical-group statement left.** Lemma 4.3 is proved for the actual hexagon H(7)
(`F7 = ZMod 7`), by kernel computation and quadric point counts, with no hypotheses. The analytic core of Lemma 4.4
(the character-sum bound, for every linear isometry of `(F7^7, Qf)`) and the final numerics are proved too. Theorem 4.5
is proved for H(7), in both readings and every block pattern, from **one explicit hypothesis, `LinearLift`**:
a collineation of H(7) with no fixed point is induced by a linear isometry `T` of `(F7^7, Qf)` with
`dim ker (T + T⁻¹ − c) ≤ 4` for all `c` (the G₂(7) structure used in the note). `LinearLift` is not proved here.
Everything builds. No `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`. `Axioms.out.txt` shows only `propext`,
`Classical.choice`, `Quot.sound`. All new files are under `lean/BipartiteDD/LeanMaxx/Omega45b/`. The branch also carries
`LeanMaxx/Omega45` (the previous job, merged unchanged from `claude/thm-omega45-q7-formalize-0ih1sy`) and what it needs
(`Omega2`, `Omega3`, `Projection`).

## Headline theorems

| theorem | file | status |
|---|---|---|
| `bonferroni_of_hex : Hex G7 klass 7 → Bonferroni G7 klass 0 4 140` (**Lemma 4.3 for H(7)**) | `Assemble.lean` | **proved** |
| `count_QF_le`: for a linear isometry `T`, `#{v : Qf v = 0 ∧ Bf v (T v) = 0} ≤ 7⁵ + 6 Σ_c 7^((3+d_c)/2)`, `d_c = dim ker (T + T⁻¹ − c)`; `sum_dk_le : Σ_c d_c ≤ 7` (**the character-sum core of Lemma 4.4**) | `CharSum.lean` | **proved** |
| `sum_rpow_lt`: `d_c ≤ 4`, `Σ d_c ≤ 7` give `Σ_c 7^((3+d_c)/2) < 1344` (the note's Schur-convexity step) | `Lemma44Lin.lean` | **proved** |
| `lemma44_of_linearLift : LinearLift → Lemma44` | `Lemma44Lin.lean` | **proved** |
| `omega45_H7_of_linearLift : LinearLift → … 9 ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam` (**Theorem 4.5, H(7), both readings, α ≥ 1, 2α ≤ 10**) | `Lemma44Lin.lean` | **proved modulo `LinearLift`** |
| `omega45_H7_geometric : Lemma44 → …` (same, from `Lemma44` directly) | `PerpQuadric.lean` | proved modulo `Lemma44` |
| `LinearLift` (collineations without fixed point are linear isometries with `d_c ≤ 4`; i.e. the G₂(7) structure) | `Lemma44Lin.lean` | **not proved** |
| `Lemma44` (**Lemma 4.4**, stated on the quadric: a collineation of H(7) with no fixed point moves ≤ 4144 points `s` to a point `p` with `Bf s p = 0`) | `PerpQuadric.lean` | follows from `LinearLift`, not proved outright |

`G7` is `incGraph (hexInc (F := F7))`. The hypothesis of `omega45_H7_geometric` is a plain definition (`Lemma44`) with no
instance arguments; `perpBound_of_lemma44` turns it into the abstract `PerpBound G7 klass 0 4144` of `Omega45/Q7.lean`.

## What was proved for Lemma 4.3, and how it differs from the note

The note proves "at least 6 forced perpendicular pairs" in 9 of 17 degenerate types (353 labelled configurations).
The reduction in `Omega45/Q7.lean` needs only **4** (`Bonferroni … 4 140`; the note remarks that 4·19608 > 15·4144 is
enough). With "fewer than 4 of the 15 pairs close" the type analysis collapses to three cases, so the 353
configurations are not enumerated:

* a collinear triple of singular points is pairwise perpendicular (3 close pairs);
* three points `t, yᵢ, yⱼ` on a projective line (an *aligned pair*, overlap empty) give 3 close pairs `(t,yᵢ), (t,yⱼ), (yᵢ,yⱼ)`;
* two such structures need ≥ 5 close pairs. So at most one pair is aligned or at most one triple is collinear,
  and not both (`special_le`, a 2¹⁵-case kernel check).

Then `bonf3` (Bonferroni, level 3, five sets) and the numbers `|C_y| ≤ 2401 = q⁴` (the existing `card_ballOpp_four_le_exact`),
pair overlap `≥ 336 = q³ − q`, triple overlap `≤ 64 = (q+1)²` give `|⋃ Cᵢ| ≤ 9621` (worst case: one aligned pair;
`12005 − 9·336 + 10·64`), and `9621 + 140·49 < 7⁵`. The overlap numbers are Lemma 4.1:

* `card_perpZeros_two`: for independent singular `y, y'`, `⟨y,y'⟩^⊥` has exactly `2401` zeros of `Qf`;
* `card_perpZeros_three_le`: for independent singular `y, y', y''`, `⟨y,y',y''⟩^⊥` has `≤ 385` zeros (`≤ 64` points).

Proof: diagonalise `Qf` on the perp space (`QuadraticForm.equivalent_weightedSumSquares`), count zeros of a diagonal form
over `F7` by a kernel table indexed by square classes (`Zcount.lean`: `wzeros5`, `wzeros4`), and control the number of zero
weights through the radical `S ∩ S^⊥`, i.e. the kernel of the Gram matrix of `S` (zero diagonal, so rank 1 never
occurs). The bridge "distance ≤ 4 between points ⟺ `Bf = 0`" (`Bridge.lean`, any odd characteristic) uses `exists_mid` for
the hard direction, so no point count is needed.

## What is left of Lemma 4.4, and why

The note's proof has four parts. Done here: **(b)** the count `#{Q = F = 0}` with ranks (`count_QF_le`; instead of Gauss sums
the proof uses exact zero counts of a quadratic form on `F7^7` with a radical of size `7^k`: `7^6` zeros for `k` even,
`≤ 7^6 + 6·7^((5+k)/2)` for `k` odd, by diagonalisation and a kernel table over square classes, `Diag7.lean`; then
`Σ_c #{R_c = 0} = 7·#{Q = F = 0} + #{Q ≠ 0}`), the radical of `R_c` (`RcQ_polar`, `card_rad_RcQ`), `Σ_c d_c ≤ 7`, and **(d)**
the numerics (`sum_rpow_lt`: the maximum is at `(4, 3, 0, …)`, `< 1344`) and the vector/point count. Not done:

* **(a)** every collineation of H(7) is induced by a linear isometry (`Aut H(7) = G₂(7) ≤ SO(7,7)`; classification, the
  fundamental theorem for the polar space Q(6,q); not in Mathlib, not in this repo);
* **(c)** `d_c ≤ 4` for fixed-point-free elements: `c = ±2` and split `c` are elementary, but for irreducible `x² − cx + 1`
  an eigenvalue of multiplicity three needs the G₂ eigenvalue structure (`1, x, y, xy` and inverses, so `μ³ = 1`).
  This cannot be dropped: `μ·I₃ ⊕ μ⁻¹·I₃ ⊕ 1` is an isometry of `(F7^7, Qf)` with `d_c = 6` and no singular eigenvector, and
  `d_c = 6` makes the bound ≈ 9295, above the thresholds 4481 (`k = 4`) and 6722 (the note's `k = 6`).

`LinearLift` packages (a) and (c). No weaker route was found:

* A spectral argument on the distance-regular point graph gives nothing: the Bose–Mesner constraints on
  `n_i = #{s : d(s, h s) = i}` are only `n_i ≥ 0`, `Σ n_i = N`, `n_0 = 0` (argued in this note; not formalised).
* An exhaustive count over G₂(7) (order 6.6·10¹¹) is infeasible even up to conjugacy without a proved class list.

## Files (`lean/BipartiteDD/LeanMaxx/Omega45b/`)

| file | content |
|---|---|
| `Defs.lean` | `F7 = ZMod 7`, `perpZeros` |
| `Zcount.lean` | `wzeros5`, `wzeros4`: zero counts of diagonal forms over `F7` (kernel tables via square classes) |
| `QuadCount.lean` | `card_perpZeros_two`, `card_perpZeros_three_le` (Lemma 4.1 counts) |
| `Bridge.lean` | `dist_inl_le_four_iff`, `dist_inl_eq_six_iff` (distance ≤ 4 / = 6 between points ⟺ `Bf = 0` / `≠ 0`) |
| `Points.lean` | `card_pts_mul` (6 vectors per point), `perp_of_dependent` (collinear triples are perpendicular) |
| `Bonf.lean` | `bonf3`, `union_bound` (abstract Bonferroni + three degenerate cases) |
| `Assemble.lean` | `pair_overlap`, `triple_overlap`, `bonferroni_of_hex` |
| `Main.lean` | `omega45_H7_of_perpBound` (instance-parametrised) |
| `PerpQuadric.lean` | `Lemma44`, `perpBound_of_lemma44`, `omega45_H7_geometric` |
| `Diag7.lean` | `wzeros7`: zero counts of diagonal forms in seven variables over `F7` (kernel table, 3⁷ square-class patterns) |
| `CharSum.lean` | `count_QF_le`, `sum_dk_le`, `RcQ_polar`, `card_rad_RcQ` |
| `Lemma44Lin.lean` | `sum_rpow_lt`, `card_pts_perp`, `LinearLift`, `lemma44_of_linearLift`, `omega45_H7_of_linearLift` |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` of the above |

## Build and check (reproduce)

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Omega45b.Lemma44Lin       # ~ 1 min on top of the Omega45 build (Tab7 ~ 7 min, ~ 7 GB)
    lake env lean BipartiteDD/LeanMaxx/Omega45b/Axioms.lean

`grep -nE "sorry|admit|native_decide|implemented_by|unsafe" lean/BipartiteDD/LeanMaxx/Omega45b/*.lean` has no hits.
`Diag7.lean` is one kernel check over 2187 cases split in two levels (a single `decide +kernel` over all of them was killed
for memory); a lemma stated with `Finset.card_filter_add_card_filter_not` over `V7 F7` made `CharSum.lean` blow past 13 GB
(kernel unfolding of a `7⁷`-element instance) and is replaced by `Finset.filter_not` and `card_sdiff`.
A first version of `Bonf.lean` used one `omega` over 40 variables and was killed for memory by `lake build` (exit 137);
it is now six small group lemmas plus a linear sum.

## Differences from the note, and checks

1. Lemma 4.3 is proved in the `k = 4` form (see above), which is what the final double count uses; the note's `k = 6`
   is not formalised, and neither are the 17 types.
2. Numerical sanity checks (Python, over F₇, random configurations): `|⟨y,y'⟩^⊥ ∩ Q| = 2401` in 400/400; pair overlaps
   `∈ {336, 343, 350}` points; `|⟨y,y',y''⟩^⊥ ∩ Q| ∈ {301, 343, 385}` vectors. These match the Lean statements.
3. The earlier report (`omega45`) said the hard direction of the bridge needs `|x^⊥ ∩ Q(6,q)| = q⁴+…+1`. It does not:
   `exists_mid` (a walk of length 4 between perpendicular points) gives it directly.
