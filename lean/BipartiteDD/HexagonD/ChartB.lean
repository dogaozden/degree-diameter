import BipartiteDD.HexagonD.ChartA

/-! Theorem D, slice 2, part 14 (target 4, step 3, chart `u₅ = 0`, `u₂ ≠ 0`): the closed-form identity.

For `u` singular with `u₀ + c u₄ = 1`, `u₅ = 0`, `u₂ ≠ 0` and `s ∈ F`, put `z = (-1/u₂, s)` (so `u ∈ Π_z`).
`XB c u s` is a point of the `S_z`-line through `u` in `Π`, and
`ν(X) + s³/(α² + c s²) = (u₂ s + u₃)/(c u₂)` (`research/p4/hats/proof/verify_closed2.py`). -/

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The point `X` of the `S_z`-line through `u`, chart `u₅ = 0`. -/
def XB (c : F) (u : V7 F) (s : F) : V7 F :=
![c*u 2*(c*u 2*u 4*s - u 2*s - u 3),
  -c*u 1*u 2^2*s - c*u 4^2 - u 2*u 3*s - u 3^2,
  -c*u 2^3*s,
  -c*u 2*(u 2*u 3*s + u 4),
  -u 2*(c*u 2*u 4*s - u 2*s - u 3),
  -c*u 2^2,
  -c^2*u 2*u 4^2*s + c*u 1*u 2 - c*u 2*u 3^2*s + 2*c*u 2*u 4*s - u 2*s - u 3]

theorem XB_mem_plane (c : F) (u : V7 F) (s : F) (hQ : Qf u = 0) (hL : u 0 + c * u 4 = 1)
    (hu5 : u 5 = 0) (hu2 : u 2 ≠ 0) : XB c u s ∈ plane u := by
  rw [mem_plane]
  have h0 : u 0 = 1 - c * u 4 := by linear_combination hL
  have h6 : u 6 = (u 3 ^ 2 - (1 - c * u 4) * u 4) / u 2 := by
    field_simp
    simp only [Qf] at hQ
    rw [h0, hu5] at hQ
    linear_combination hQ
  ext k
  fin_cases k <;> simp [zmul, phi, XB, hu5] <;> (try simp only [h0, h6]) <;> field_simp <;> ring

theorem XB_0 (c : F) (u : V7 F) (s : F) : XB c u s 0 = c*u 2*(c*u 2*u 4*s - u 2*s - u 3) := rfl
theorem XB_2 (c : F) (u : V7 F) (s : F) : XB c u s 2 = -c*u 2^3*s := rfl
theorem XB_3 (c : F) (u : V7 F) (s : F) : XB c u s 3 = -c*u 2*(u 2*u 3*s + u 4) := rfl
theorem XB_4 (c : F) (u : V7 F) (s : F) : XB c u s 4 = -u 2*(c*u 2*u 4*s - u 2*s - u 3) := rfl
theorem XB_5 (c : F) (u : V7 F) (s : F) : XB c u s 5 = -c*u 2^2 := rfl

theorem XB_L (c : F) (u : V7 F) (s : F) : XB c u s 0 + c * XB c u s 4 = 0 := by
  rw [XB_0, XB_4]; ring

theorem XB_Lz (c : F) (u : V7 F) (s : F) (hu2 : u 2 ≠ 0) :
    Lz c (-1 / u 2) s (XB c u s) = 0 := by
  have := XB_L c u s
  simp only [Lz]
  have h2 : -1 / u 2 * XB c u s 2 + s * XB c u s 5 = 0 := by
    rw [XB_2, XB_5]
    field_simp
    ring
  linear_combination this + h2

theorem XB_ne {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu2 : u 2 ≠ 0) :
    c * XB c u s 2 ^ 2 + XB c u s 5 ^ 2 ≠ 0 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  refine aniso_ne hc ?_
  rintro ⟨-, h5⟩
  rw [XB_5] at h5
  exact mul_ne_zero hc0 (pow_ne_zero 2 hu2) (by linear_combination -h5)

theorem XB_nonzero {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu2 : u 2 ≠ 0) :
    XB c u s ≠ 0 := by
  intro h
  apply XB_ne hc u s hu2
  rw [h]; simp

theorem zB_ne {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu2 : u 2 ≠ 0) :
    (-1 / u 2) ^ 2 + c * s ^ 2 ≠ 0 := by
  have : (-1 / u 2) ^ 2 + c * s ^ 2 = c * s ^ 2 + (1 / u 2) ^ 2 := by ring
  rw [this]
  refine aniso_ne hc ?_
  rintro ⟨-, h2⟩
  have : 1 / u 2 = 0 := by simpa using h2
  simp at this
  exact hu2 this

/-- The affine identity of step 3 (chart `u₅ = 0`). -/
theorem XB_nu {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu2 : u 2 ≠ 0) :
    nuf c (XB c u s) + s ^ 3 / ((-1 / u 2) ^ 2 + c * s ^ 2) = (u 2 * s + u 3) / (c * u 2) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by simp⟩
  have hΛ : c * (u 2 * s) ^ 2 + 1 ^ 2 ≠ 0 := aniso_ne hc (fun h => one_ne_zero h.2)
  have hZ : (-1 / u 2) ^ 2 + c * s ^ 2 = (c * (u 2 * s) ^ 2 + 1 ^ 2) / u 2 ^ 2 := by
    field_simp
    ring
  have hD : c * XB c u s 2 ^ 2 + XB c u s 5 ^ 2 = c ^ 2 * u 2 ^ 4 * (c * (u 2 * s) ^ 2 + 1 ^ 2) := by
    rw [XB_2, XB_5]; ring
  have hs3 : s ^ 3 / ((c * (u 2 * s) ^ 2 + 1 ^ 2) / u 2 ^ 2) =
      s ^ 3 * u 2 ^ 2 / (c * (u 2 * s) ^ 2 + 1 ^ 2) := by
    field_simp
  unfold nuf
  rw [hZ, hs3, hD, XB_2, XB_3, XB_4, XB_5]
  have hDne : c ^ 2 * u 2 ^ 4 * (c * (u 2 * s) ^ 2 + 1 ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) (pow_ne_zero 4 hu2)) hΛ
  have hFne : c * u 2 ≠ 0 := mul_ne_zero hc0 hu2
  rw [div_add_div _ _ hDne hΛ, div_eq_div_iff (mul_ne_zero hDne hΛ) hFne]
  ring

end BipartiteDD.HexagonD
