import BipartiteDD.LeanMaxx.Omega45b.Assemble
import BipartiteDD.LeanMaxx.Omega45.Dual7
import BipartiteDD.LeanMaxx.Omega3.Concrete

/-!
# Theorem 4.5 at `H(7)` with Lemma 4.3 proved: one hypothesis left

`omega45_H7_of_perpBound`: for the incidence graph `G7` of the split Cayley hexagon `H(7)` (`F7 = ZMod 7`),
every geometric labelling of Gómez's wiring (both readings, every block pattern with `α ≥ 1` blocks, `2 α ≤ 10`)
gives diameter `≥ 9`, **assuming only Lemma 4.4**: `PerpBound G7 klass 0 4144` (a collineation of `H(7)` without a
fixed point moves at most `4144` points to a point at distance `≤ 4`). Lemma 4.3 (`Bonferroni`) is no longer a
hypothesis: it is `bonferroni_of_hex`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45

/-- **Theorem 4.5 at `H(7)`, modulo Lemma 4.4 only.** -/
theorem omega45_H7_of_perpBound [Fintype (SPt F7 ⊕ HLine F7)] [DecidableEq (SPt F7 ⊕ HLine F7)]
    [DecidableRel G7.Adj] (H : Hex G7 klass 7) [Nonempty (SPt F7 ⊕ HLine F7)] {α : ℕ} (hα : 0 < α)
    (h2 : 2 * α ≤ 7 + 3) (typ : Fin α → Bool) (ε₀ : ZMod 2) (hε : ε₀ = 0 ∨ ε₀ + 1 = 0)
    (μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7)) (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : Geometric G7 klass μ) (hP : PerpBound G7 klass 0 4144) :
    (9 : ℕ∞) ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam :=
  omega45_geometric_of_hyps_points H hα h2 typ 0 ε₀ hε μ hμ hgeo hP (bonferroni_of_hex H)

end BipartiteDD.LeanMaxx.Omega45b
