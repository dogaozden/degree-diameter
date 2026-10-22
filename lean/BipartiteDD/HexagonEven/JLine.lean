import BipartiteDD.HexagonEven.Identity

/-! Theorem D (even `q`), algebraic core, part 2 (mirror of `HexagonD/Identity/Line.lean`): for a nonzero singular
point `x ∈ Π_z`, the pair `(x, J x)` satisfies `IsHPair` and `⟨x, J x⟩` is a line of `H(q)` lying in `Π_z`.
`J x` is not a multiple of `x`: otherwise `J² x = c² x = c x + d x`, i.e. `c² + c + d = 0`, which `hd` forbids. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

theorem isHPair_JE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) (hQ : Qf x = 0) :
    IsHPair x (JE d α β x) :=
  ⟨hQ, by rw [Qf_JE hx h2, hQ, mul_zero], by rw [Bf_JE hx h2, hQ], tits_JE hx h2 hQ⟩

theorem span_InPiZE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) {v : V7 F}
    (hv : v ∈ span F {x, JE d α β x}) : InPiZE d α β v := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
  have hJ := InPiZE_JE d α β x h2
  unfold InPiZE at hx hJ ⊢
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * hx + b * hJ

theorem JE_not_mem_span {d α β : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {x : V7 F}
    (hx0 : x ≠ 0) (hx : InPiZE d α β x) : JE d α β x ∉ span F {x} := by
  intro h
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
  have e1 := JE_JE hx h2
  have e2 : JE d α β (JE d α β x) = (c * c) • x := by
    rw [← hc, JE_smul, ← hc, smul_smul]
  have h3 : (c * c) • x = c • x + d • x := by
    rw [← e2, e1, hc]
  have h5 : (c * c - c - d) • x = 0 := by
    rw [sub_smul, sub_smul, h3]
    abel
  rcases smul_eq_zero.1 h5 with h | h
  · exact hd c (by linear_combination h + (c + d) * h2)
  · exact hx0 h

/-- `⟨x, J x⟩` is a line of `H(q)` in `Π_z`, for a nonzero singular point `x ∈ Π_z`. -/
theorem exists_hline_JE {d α β : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {x : V7 F}
    (hx0 : x ≠ 0) (hQ : Qf x = 0) (hx : InPiZE d α β x) :
    ∃ W : HLine F, W.1 = span F {x, JE d α β x} ∧ ∀ v ∈ W.1, InPiZE d α β v :=
  ⟨hlineOf hx0 (isHPair_JE hx h2 hQ) (JE_not_mem_span hd h2 hx0 hx), rfl,
    fun _ hv => span_InPiZE hx h2 hv⟩

end BipartiteDD.HexagonEven
