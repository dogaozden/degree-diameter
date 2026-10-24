import BipartiteDD.Haar.D6D10d.Cover
import BipartiteDD.Haar.Diam10

/-! The covering hypothesis of the Δ6·D10 record, from the stage checks of `Cover`.

`CoverD` is the hypothesis of `haar_isBipartiteDegDiam10_of_equiv`, written in this module, which imports `Diam10`, so
that its group operations are elaborated in the same instance context as the lemma's. The word `wordC` of `Words` is
related to the nested product by `wordOf_eq`, which holds for every group by `rfl`. -/

namespace BipartiteDD.Haar.D6D10d

/-- The nine-letter covering hypothesis of `Diam10`, for a general group. -/
def CoverD {H : Type*} [Group H] (S : Finset H) : Prop :=
  ∀ g : H, ∃ x₁ ∈ S, ∃ x₂ ∈ S, ∃ x₃ ∈ S, ∃ x₄ ∈ S, ∃ x₅ ∈ S, ∃ x₆ ∈ S, ∃ x₇ ∈ S, ∃ x₈ ∈ S,
    ∃ x₉ ∈ S, g = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉)))))))

theorem wordOf_eq {H : Type*} [Group H] (x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ : H) :
    wordOf x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ x₉ = x₁ * (x₂⁻¹ * (x₃ * (x₄⁻¹ * (x₅ * (x₆⁻¹ * (x₇ * (x₈⁻¹ * x₉))))))) :=
  rfl

theorem cover : CoverD SS := by
  unfold CoverD
  intro g
  obtain ⟨c, hc⟩ := exC (idxG g) (idxG_lt g)
  rw [gOf_idxG] at hc
  unfold wordC at hc
  rw [wordOf_eq] at hc
  refine ⟨sG (dig c 0), sG_mem _ (dig_lt c 0), sG (dig c 1), sG_mem _ (dig_lt c 1),
    sG (dig c 2), sG_mem _ (dig_lt c 2), sG (dig c 3), sG_mem _ (dig_lt c 3),
    sG (dig c 4), sG_mem _ (dig_lt c 4), sG (dig c 5), sG_mem _ (dig_lt c 5),
    sG (dig c 6), sG_mem _ (dig_lt c 6), sG (dig c 7), sG_mem _ (dig_lt c 7),
    sG (dig c 8), sG_mem _ (dig_lt c 8), hc⟩

end BipartiteDD.Haar.D6D10d
