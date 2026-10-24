import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Finset.Basic

/-! The nine-letter covering word of a group, and the covering hypothesis `CoverHyp` of `Diam10` written as a
definition, so that its unfolding matches the word term for term (see research/lean-haarD/STATUS-d6D10c.md). -/

namespace BipartiteDD.Haar.D6D10d

/-- The nine-letter alternating word `x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉` in a group, right-nested. -/
def wordOf {G : Type*} [Group G] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : G) : G :=
  x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

/-- The covering hypothesis of `haar_isBipartiteDegDiam10_of_equiv`, for a general group. -/
def CoverHyp {G : Type*} [Group G] (S : Finset G) : Prop :=
  ∀ g : G, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

end BipartiteDD.Haar.D6D10d
