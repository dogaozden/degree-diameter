import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic

/-! The nine-letter covering word and its covering hypothesis, for a general group.

`wordOf x₁ … x₉` is `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉`, right-nested. `CoverHyp S` is the hypothesis of
`BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`) written with the same group operations, so
the record passes a proof of `CoverHyp SS` directly (see research/lean-haarD/BRIEF.md, the `CoverHyp` fix). -/

namespace BipartiteDD.Haar.D4D10b

/-- The nine-letter alternating word, right-nested. -/
def wordOf {G : Type*} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : G) : G :=
  x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

/-- Every element of `G` is a nine-letter word in `S` (the covering condition of `Diam10`). -/
def CoverHyp {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

end BipartiteDD.Haar.D4D10b
