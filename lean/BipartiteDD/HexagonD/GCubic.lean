import BipartiteDD.HexagonD.FreeLines

/-! Theorem D, slice 2, part 19 (target 4): the binary cubic `G`.

For every finite field `F` with `-c` a non-square there are `c₀, c₁` such that
`G(a, b) = (c₀ a + c₁ b)(a² + c b²) - b³` has no zero on `F² ∖ 0` (`exists_goodCubic`).

Proof (as in the report): `G(a, 0) = c₀ a³ ≠ 0` if `c₀ ≠ 0`, and `G(a, b) = b³ ((c₀ t + c₁)(t² + c) - 1)`
with `t = a/b`. The map `(t, c₀) ↦ (c₀, (t² + c)⁻¹ - c₀ t)` from `F × F^×` to `F^× × F` would be onto if every
`(c₀, c₁)` were bad; it is not injective (`(0, c₀*)` and `(1, c₀*)` have the same image for
`c₀* = -1/(c(1 + c))`), hence not onto. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

variable {F : Type*} [Field F] [Fintype F] {c : F}

theorem exists_goodCubic (hc : ¬ IsSquare (-c)) : ∃ c0 c1 : F, GoodCubic c c0 c1 := by
  classical
  by_contra hno
  push Not at hno
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  have hsq : ∀ t : F, t ^ 2 + c ≠ 0 := fun t h => hc ⟨t, by linear_combination -h⟩
  have hex : ∀ (c0 : F), c0 ≠ 0 → ∀ c1 : F, ∃ t, (c0 * t + c1) * (t ^ 2 + c) = 1 := by
    intro c0 hc0 c1
    by_contra h
    push Not at h
    apply hno c0 c1
    intro a b hab hG
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := fun h => hab ⟨h, rfl⟩
      have : c0 * a * a ^ 2 = 0 := by simpa using hG
      exact mul_ne_zero (mul_ne_zero hc0 ha) (pow_ne_zero 2 ha) this
    · apply h (a / b)
      field_simp
      linear_combination hG
  let f : F × {c0 : F // c0 ≠ 0} → {c0 : F // c0 ≠ 0} × F := fun x =>
    (x.2, (x.1 ^ 2 + c)⁻¹ - x.2.1 * x.1)
  have hsurj : Function.Surjective f := by
    rintro ⟨⟨c0, h0⟩, c1⟩
    obtain ⟨t, ht⟩ := hex c0 h0 c1
    refine ⟨(t, ⟨c0, h0⟩), ?_⟩
    simp only [f]
    refine Prod.ext rfl ?_
    show (t ^ 2 + c)⁻¹ - c0 * t = c1
    have : c0 * t + c1 = (t ^ 2 + c)⁻¹ := by
      exact eq_inv_of_mul_eq_one_left ht
    linear_combination -this
  have hcard : Fintype.card (F × {c0 : F // c0 ≠ 0}) = Fintype.card ({c0 : F // c0 ≠ 0} × F) := by
    simp only [Fintype.card_prod]; ring
  have hinj : Function.Injective f := (Fintype.bijective_iff_surjective_and_card f).2 ⟨hsurj, hcard⟩ |>.1
  -- the collision
  have h1c : (1 : F) + c ≠ 0 := fun h => hc ⟨1, by linear_combination -h⟩
  have hstar : (-1 / (c * (1 + c)) : F) ≠ 0 := by
    have := mul_ne_zero hc0 h1c
    simpa using this
  have := hinj (a₁ := (0, ⟨-1 / (c * (1 + c)), hstar⟩)) (a₂ := (1, ⟨-1 / (c * (1 + c)), hstar⟩)) (by
    simp only [f]
    refine Prod.ext rfl ?_
    show ((0 : F) ^ 2 + c)⁻¹ - (-1 / (c * (1 + c))) * 0 = ((1 : F) ^ 2 + c)⁻¹ - (-1 / (c * (1 + c))) * 1
    field_simp
    linear_combination (1 + c) * mul_inv_cancel₀ hc0)
  simp at this

end BipartiteDD.HexagonD
