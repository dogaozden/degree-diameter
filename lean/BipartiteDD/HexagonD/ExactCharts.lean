import BipartiteDD.HexagonD.ExactFamily

/-! Theorem D, slice 2, part 17 (target 4, step 4): a free point is on exactly one line of `Wset`.

The two charts `u₅ ≠ 0` and `u₅ = 0 ≠ u₂` instantiate `exact_of_family`. The equation
`ν(X(z)) = F(z)` along the affine line `A_u` is a linear equation in the parameter `s` whose coefficient is
`G(u₅, -u₂) ≠ 0` (hypothesis `hG`: the binary cubic `G(a, b) = (c₀ a + c₁ b)(a² + c b²) - b³` has no
nontrivial zero). -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

theorem Fz_eq (c c0 c1 : F) {A B : F} (hD : A ^ 2 + c * B ^ 2 ≠ 0) :
    Fz c c0 c1 (A, B) = c0 * A + c1 * B - B ^ 3 / (A ^ 2 + c * B ^ 2) := by
  simp only [Fz]
  generalize A ^ 2 + c * B ^ 2 = D at hD ⊢
  field_simp

theorem eq_Fz_iff (c c0 c1 : F) {A B : F} (hD : A ^ 2 + c * B ^ 2 ≠ 0) (n : F) :
    n = Fz c c0 c1 (A, B) ↔ n + B ^ 3 / (A ^ 2 + c * B ^ 2) = c0 * A + c1 * B := by
  rw [Fz_eq c c0 c1 hD, eq_sub_iff_add_eq]

/-- The cubic `G` has no nontrivial zero. -/
def GoodCubic (c c0 c1 : F) : Prop :=
  ∀ a b : F, ¬ (a = 0 ∧ b = 0) → (c0 * a + c1 * b) * (a ^ 2 + c * b ^ 2) - b ^ 3 ≠ 0

theorem exact_chartA (hc : ¬ IsSquare (-c)) {c0 c1 : F} (hG : GoodCubic c c0 c1) {u : V7 F}
    (hQ : Qf u = 0) (hL : u 0 + c * u 4 = 1) (hu5 : u 5 ≠ 0) :
    ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ u ∈ m.1 := by
  have hU : c * u 2 ^ 2 + u 5 ^ 2 ≠ 0 := aniso_ne hc (fun h => hu5 h.2)
  have hK : (c0 * u 5 + c1 * (-u 2)) * (u 5 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3 ≠ 0 :=
    hG _ _ (fun h => hu5 h.1)
  have hnu : ∃! s, nuf c (XA c u s) = Fz c c0 c1 (s * u 5, -1 / u 5 - s * u 2) := by
    have hden : u 5 * (c * u 2 ^ 2 + u 5 ^ 2) ≠ 0 := mul_ne_zero hu5 hU
    have hiff : ∀ s, nuf c (XA c u s) = Fz c c0 c1 (s * u 5, -1 / u 5 - s * u 2) ↔
        s * (-(u 5 * ((c0 * u 5 + c1 * -u 2) * (u 5 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3))) = (u 2 ^ 2 - u 2 * u 3 * u 5 + u 4 * u 5 ^ 2) - c1 * (c * u 2 ^ 2 + u 5 ^ 2) := by
      intro s
      rw [eq_Fz_iff c c0 c1 (zA_ne hc u s hu5), XA_nu hc u s hu5]
      have hid : -(u 2 ^ 3 * u 5 * s + u 2 ^ 2 - u 2 * u 3 * u 5 + u 4 * u 5 ^ 2) /
          (u 5 * (c * u 2 ^ 2 + u 5 ^ 2)) - (c0 * (s * u 5) + c1 * (-1 / u 5 - s * u 2)) =
          (s * (-(u 5 * ((c0 * u 5 + c1 * -u 2) * (u 5 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3))) - ((u 2 ^ 2 - u 2 * u 3 * u 5 + u 4 * u 5 ^ 2) - c1 * (c * u 2 ^ 2 + u 5 ^ 2))) / (u 5 * (c * u 2 ^ 2 + u 5 ^ 2)) := by
        rw [eq_div_iff hden, sub_mul, div_mul_cancel₀ _ hden]
        field_simp
        ring
      rw [← sub_eq_zero, hid, div_eq_zero_iff]
      constructor
      · rintro (h | h)
        · linear_combination h
        · exact absurd h hden
      · intro h
        left
        linear_combination h
    have hs0 : -(u 5 * ((c0 * u 5 + c1 * -u 2) * (u 5 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3)) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hu5 hK)
    exact ⟨_, (hiff _).2 (div_mul_cancel₀ _ hs0), fun s hs => (eq_div_iff hs0).2 ((hiff s).1 hs)⟩
  refine exact_of_family hc c0 c1 hQ hL (XA c u) (fun s => (s * u 5, -1 / u 5 - s * u 2))
    (fun s => XA_mem_plane c u s hQ hL hu5) (XA_L c u) (fun s => XA_Lz c u s hu5)
    (fun s => XA_nonzero hc u s hu5) ?_ ?_ hnu
  · intro s
    field_simp
    ring
  · intro a b h
    refine ⟨a / u 5, Prod.ext ?_ ?_⟩
    · show a / u 5 * u 5 = a
      field_simp
    · show -1 / u 5 - a / u 5 * u 2 = b
      field_simp
      linear_combination -h

theorem exact_chartB (hc : ¬ IsSquare (-c)) {c0 c1 : F} (hG : GoodCubic c c0 c1) {u : V7 F}
    (hQ : Qf u = 0) (hL : u 0 + c * u 4 = 1) (hu5 : u 5 = 0) (hu2 : u 2 ≠ 0) :
    ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ u ∈ m.1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  have hK : (c0 * 0 + c1 * (-u 2)) * (0 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3 ≠ 0 :=
    hG _ _ (fun h => hu2 (neg_eq_zero.1 h.2))
  have hK' : 1 - c * c1 ≠ 0 := by
    intro h
    apply hK
    have : (c0 * 0 + c1 * (-u 2)) * (0 ^ 2 + c * (-u 2) ^ 2) - (-u 2) ^ 3 = u 2 ^ 3 * (1 - c * c1) := by ring
    rw [this, h, mul_zero]
  have hnu : ∃! s, nuf c (XB c u s) = Fz c c0 c1 (-1 / u 2, s) := by
    have hiff : ∀ s, nuf c (XB c u s) = Fz c c0 c1 (-1 / u 2, s) ↔
        s * (u 2 * (1 - c * c1)) = -(u 3 + c * c0) := by
      intro s
      rw [eq_Fz_iff c c0 c1 (zB_ne hc u s hu2), XB_nu hc u s hu2]
      have hid : (u 2 * s + u 3) / (c * u 2) - (c0 * (-1 / u 2) + c1 * s) =
          (s * (u 2 * (1 - c * c1)) + (u 3 + c * c0)) / (c * u 2) := by
        field_simp
        ring
      rw [← sub_eq_zero, hid, div_eq_zero_iff]
      constructor
      · rintro (h | h)
        · linear_combination h
        · exact absurd h (mul_ne_zero hc0 hu2)
      · intro h
        left
        linear_combination h
    have hs0 : u 2 * (1 - c * c1) ≠ 0 := mul_ne_zero hu2 hK'
    exact ⟨_, (hiff _).2 (div_mul_cancel₀ _ hs0), fun s hs => (eq_div_iff hs0).2 ((hiff s).1 hs)⟩
  refine exact_of_family hc c0 c1 hQ hL (XB c u) (fun s => (-1 / u 2, s))
    (fun s => XB_mem_plane c u s hQ hL hu5 hu2) (XB_L c u) (fun s => XB_Lz c u s hu2)
    (fun s => XB_nonzero hc u s hu2) ?_ ?_ hnu
  · intro s
    show -1 / u 2 * u 2 + s * u 5 = -1
    rw [hu5]
    field_simp
    ring
  · intro a b h
    refine ⟨b, Prod.ext ?_ rfl⟩
    show -1 / u 2 = a
    rw [hu5] at h
    field_simp
    linear_combination -h

end BipartiteDD.HexagonD
