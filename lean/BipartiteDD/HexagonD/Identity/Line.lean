import BipartiteDD.HexagonD.Identity.Jz

/-! Theorem D, algebraic core, part 2: the line `⟨x, J_z x⟩` of `H(q)` in `Π_z`.

For a nonzero singular point `x ∈ Π_z`, the pair `(x, J_z x)` satisfies `IsHPair` (`isHPair_Jz`), `J_z x` is not a
multiple of `x` (`Jz_not_mem_span`: otherwise `J_z² x = -c x` would force `-c` to be a square), so
`hlineOf` gives a line of `H(q)`, which is `⟨x, J_z x⟩` and lies in `Π_z` (`exists_hline_Jz`). -/

namespace BipartiteDD.HexagonD.Identity

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

theorem isHPair_Jz {c α β : F} {x : V7 F} (hx : InPiz c α β x) (hQ : Qf x = 0) :
    IsHPair x (Jz c α β x) := by
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := tits_Jz hx
  refine ⟨hQ, ?_, Bf_Jz hx, ?_⟩
  · rw [Qf_Jz hx, hQ, mul_zero]
  · refine ⟨by linear_combination d1 + hQ, by linear_combination d2, by linear_combination d3,
      by linear_combination d4 + (-c) * hQ, by linear_combination d5 + α * hQ,
      by linear_combination d6 + (-β) * hQ⟩

theorem span_inPiz {c α β : F} {x : V7 F} (hx : InPiz c α β x) {v : V7 F}
    (hv : v ∈ span F {x, Jz c α β x}) : InPiz c α β v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hJ := InPiz_Jz c α β x
  unfold InPiz at hx hJ ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * hx + b * hJ

/-- If `J_z x` were a multiple of `x`, then `J_z² x = -c x` would give `(a² + c) x = 0`. -/
theorem Jz_not_mem_span {c α β : F} (hc : ¬ IsSquare (-c)) {x : V7 F} (hx0 : x ≠ 0)
    (hx : InPiz c α β x) : Jz c α β x ∉ span F {x} := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
  have e1 : Jz c α β (Jz c α β x) = -c • x := Jz_Jz hx
  have e2 : Jz c α β (Jz c α β x) = (a * a) • x := by
    rw [← ha, Jz_smul, ← ha, smul_smul]
  have h3 : (a * a + c) • x = 0 := by
    have h4 : (a * a) • x = -c • x := e2.symm.trans e1
    rw [add_smul, h4]
    simp
  rcases smul_eq_zero.1 h3 with h5 | h5
  · exact hc ⟨a, by linear_combination -h5⟩
  · exact hx0 h5

/-- `⟨x, J_z x⟩` is a line of `H(q)` in `Π_z`, for a nonzero singular point `x ∈ Π_z`. -/
theorem exists_hline_Jz {c α β : F} (hc : ¬ IsSquare (-c)) {x : V7 F} (hx0 : x ≠ 0) (hQ : Qf x = 0)
    (hx : InPiz c α β x) : ∃ W : HLine F, W.1 = span F {x, Jz c α β x} ∧ ∀ v ∈ W.1, InPiz c α β v := by
  refine ⟨hlineOf hx0 (isHPair_Jz hx hQ) (Jz_not_mem_span hc hx0 hx), rfl, fun v hv => ?_⟩
  exact span_inPiz hx hv

end BipartiteDD.HexagonD.Identity
