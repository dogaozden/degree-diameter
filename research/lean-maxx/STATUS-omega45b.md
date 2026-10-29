# STATUS: omega45b (q = 7, Theorem 4.5 of research/theorems/OMEGA_REPAIR.md, concrete H(7))

**Verdict: partial, one statement left.** Lemma 4.3 is now proved for the actual hexagon H(7) (`F7 = ZMod 7`), by kernel
computation and quadric point counts, with no hypotheses. Theorem 4.5 is proved for H(7), in both readings and every
block pattern, from **Lemma 4.4 alone**. Lemma 4.4 is not proved here.
Everything builds. No `sorry`, `admit`, `native_decide`, `axiom`, `unsafe`. `Axioms.out.txt` shows only `propext`,
`Classical.choice`, `Quot.sound`. All new files are under `lean/BipartiteDD/LeanMaxx/Omega45b/`. The branch also carries
`LeanMaxx/Omega45` (the previous job, merged unchanged from `claude/thm-omega45-q7-formalize-0ih1sy`) and what it needs
(`Omega2`, `Omega3`, `Projection`).

## Headline theorems

| theorem | file | status |
|---|---|---|
| `bonferroni_of_hex : Hex G7 klass 7 → Bonferroni G7 klass 0 4 140` (**Lemma 4.3 for H(7)**) | `Assemble.lean` | **proved** |
| `omega45_H7_geometric : Lemma44 → … 9 ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam` (**Theorem 4.5, H(7), both readings, α ≥ 1, 2α ≤ 10**) | `PerpQuadric.lean` | **proved modulo `Lemma44`** |
| `Lemma44` (**Lemma 4.4**, stated on the quadric: a collineation of H(7) with no fixed point moves ≤ 4144 points `s` to a point `p` with `Bf s p = 0`) | `PerpQuadric.lean` | **not proved** |

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

## Why Lemma 4.4 is not here

The note's proof needs (a) every collineation of H(7) is induced by a linear map in G₂(7) ≤ SO(7,7) (classification,
the fundamental theorem for the polar space Q(6,q); not in Mathlib, not in this repo), (b) the Gauss-sum count
`#{Q = F = 0} = q⁻² Σ ψ(aQ + bF)` with ranks, (c) the eigenvalue structure of G₂ on the 7-dimensional module
(`d_c ≤ 4`, a multiplicity-3 eigenvalue forces `μ³ = 1`), (d) the Schur-convexity step. No weaker route was found:

* A spectral argument on the distance-regular point graph gives nothing: the Bose–Mesner constraints on
  `n_i = #{s : d(s, h s) = i}` are only `n_i ≥ 0`, `Σ n_i = N`, `n_0 = 0` (argued in this note; not formalised).
* An exhaustive count over G₂(7) (order 6.6·10¹¹) is infeasible even up to conjugacy without a proved class list.
* Dropping (c) leaves `d_c ≤ 6` and the bound becomes ≈ 9295, above the threshold 4481 that the `k = 4` reduction can
  absorb (and above 6722, the threshold with the note's `k = 6`).

CHARSUM_PLACEHOLDER

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
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` of the above |

## Build and check (reproduce)

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Omega45b.PerpQuadric       # ~ 1 min on top of the Omega45 build (Tab7 ~ 7 min, ~ 7 GB)
    lake env lean BipartiteDD/LeanMaxx/Omega45b/Axioms.lean

`grep -nE "sorry|admit|native_decide|implemented_by|unsafe" lean/BipartiteDD/LeanMaxx/Omega45b/*.lean` has no hits.
A first version of `Bonf.lean` used one `omega` over 40 variables and was killed for memory by `lake build` (exit 137);
it is now six small group lemmas plus a linear sum.

## Differences from the note, and checks

1. Lemma 4.3 is proved in the `k = 4` form (see above), which is what the final double count uses; the note's `k = 6`
   is not formalised, and neither are the 17 types.
2. Numerical sanity checks (Python, over F₇, random configurations): `|⟨y,y'⟩^⊥ ∩ Q| = 2401` in 400/400; pair overlaps
   `∈ {336, 343, 350}` points; `|⟨y,y',y''⟩^⊥ ∩ Q| ∈ {301, 343, 385}` vectors. These match the Lean statements.
3. The earlier report (`omega45`) said the hard direction of the bridge needs `|x^⊥ ∩ Q(6,q)| = q⁴+…+1`. It does not:
   `exists_mid` (a walk of length 4 between perpendicular points) gives it directly.
