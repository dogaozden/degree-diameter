import BipartiteDD.HexagonD.PiZ

/-! Theorem D, slice 2, part 13 (target 4, step 3, chart `u₅ ≠ 0`): the closed-form identity.

For `u` a singular vector with `u₀ + c u₄ = 1` and `u₅ ≠ 0`, and `s ∈ F`, put `α = s u₅`, `β = -1/u₅ - s u₂`
(so `α u₂ + β u₅ = -1`, i.e. `u ∈ Π_z` for `z = (α, β)`). The vector `XA c u s` is a point of the `S_z`-line
through `u` (`XA_mem_plane`), lies in `Π` (`XA_L`), and `ν(X) + β³/(α² + cβ²)` is an explicit affine function
of `s` (`XA_nu`), where `ν(x) = (x₂x₃ - x₄x₅)/(c x₂² + x₅²)` (`nuf`). All identities are polynomial identities
with integer coefficients (`research/p4/hats/proof/verify_closed.py`). -/

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The function `ν(x) = (x₂x₃ - x₄x₅)/(c x₂² + x₅²)`. -/
def nuf (c : F) (x : V7 F) : F := (x 2 * x 3 - x 4 * x 5) / (c * x 2 ^ 2 + x 5 ^ 2)

theorem nuf_smul (c a : F) (x : V7 F) (ha : a ≠ 0) : nuf c (a • x) = nuf c x := by
  by_cases hD : c * x 2 ^ 2 + x 5 ^ 2 = 0
  · simp only [nuf, Pi.smul_apply, smul_eq_mul]
    have : c * (a * x 2) ^ 2 + (a * x 5) ^ 2 = 0 := by
      have : c * (a * x 2) ^ 2 + (a * x 5) ^ 2 = a ^ 2 * (c * x 2 ^ 2 + x 5 ^ 2) := by ring
      rw [this, hD, mul_zero]
    rw [this, hD]; simp
  · simp only [nuf, Pi.smul_apply, smul_eq_mul]
    field_simp

/-- `c a² + b² = 0` forces `a = b = 0` when `-c` is a non-square. -/
theorem aniso {c : F} (hc : ¬ IsSquare (-c)) {a b : F} (h : c * a ^ 2 + b ^ 2 = 0) : a = 0 ∧ b = 0 := by
  have ha : a = 0 := by
    by_contra ha
    exact hc ⟨b / a, by field_simp; linear_combination -h⟩
  subst ha
  refine ⟨rfl, ?_⟩
  simpa using h

theorem aniso_ne {c : F} (hc : ¬ IsSquare (-c)) {a b : F} (h : ¬ (a = 0 ∧ b = 0)) :
    c * a ^ 2 + b ^ 2 ≠ 0 := fun h' => h (aniso hc h')

/-- The point `X` of the `S_z`-line through `u`, chart `u₅ ≠ 0`. -/
def XA (c : F) (u : V7 F) (s : F) : V7 F :=
![-c*u 5*(c*u 2^2*u 4*u 5*s + c*u 2*u 4 - u 2^2*u 5*s - u 2 + u 3*u 5 + u 4*u 5^3*s),
  c^2*u 2^2*u 4^2*u 5*s + c^2*u 2*u 4^2 - c*u 2^3*u 5*u 6*s + c*u 2^2*u 3^2*u 5*s - c*u 2^2*u 4*u 5*s - c*u 2^2*u 6 + c*u 2*u 3^2 - c*u 2*u 4 + c*u 4^2*u 5^3*s + u 2*u 3*u 5^2*s - u 2*u 5^3*u 6*s + u 3^2*u 5^3*s + u 3*u 5 - u 5^2*u 6,
  u 5*(c*u 2^2 + u 5^2)*(u 2*u 5*s + 1),
  u 5*(c*u 2^2*u 3*u 5*s + c*u 2*u 3 - c*u 4*u 5 + u 2*u 5^2*s + u 3*u 5^3*s + u 5),
  u 5*(c*u 2^2*u 4*u 5*s + c*u 2*u 4 - u 2^2*u 5*s - u 2 + u 3*u 5 + u 4*u 5^3*s),
  u 5^3*s*(c*u 2^2 + u 5^2),
  u 5*(c^2*u 4^2 + c*u 2^2*u 5*u 6*s - c*u 2*u 4*u 5*s + c*u 3^2 - 2*c*u 4 + u 2*u 5*s + u 3*u 5^2*s + u 5^3*u 6*s + 1)]

theorem XA_mem_plane (c : F) (u : V7 F) (s : F) (hQ : Qf u = 0) (hL : u 0 + c * u 4 = 1)
    (hu5 : u 5 ≠ 0) : XA c u s ∈ plane u := by
  rw [mem_plane]
  have h0 : u 0 = 1 - c * u 4 := by linear_combination hL
  have h1 : u 1 = (u 3 ^ 2 - (1 - c * u 4) * u 4 - u 2 * u 6) / u 5 := by
    field_simp
    simp only [Qf] at hQ
    rw [h0] at hQ
    linear_combination hQ
  ext k
  fin_cases k <;> simp [zmul, phi, XA] <;> (try simp only [h0, h1]) <;> field_simp <;> ring

theorem XA_0 (c : F) (u : V7 F) (s : F) : XA c u s 0 =
    -c*u 5*(c*u 2^2*u 4*u 5*s + c*u 2*u 4 - u 2^2*u 5*s - u 2 + u 3*u 5 + u 4*u 5^3*s) := rfl
theorem XA_2 (c : F) (u : V7 F) (s : F) : XA c u s 2 = u 5*(c*u 2^2 + u 5^2)*(u 2*u 5*s + 1) := rfl
theorem XA_4 (c : F) (u : V7 F) (s : F) : XA c u s 4 =
    u 5*(c*u 2^2*u 4*u 5*s + c*u 2*u 4 - u 2^2*u 5*s - u 2 + u 3*u 5 + u 4*u 5^3*s) := rfl
theorem XA_5 (c : F) (u : V7 F) (s : F) : XA c u s 5 = u 5^3*s*(c*u 2^2 + u 5^2) := rfl
theorem XA_3 (c : F) (u : V7 F) (s : F) : XA c u s 3 =
    u 5*(c*u 2^2*u 3*u 5*s + c*u 2*u 3 - c*u 4*u 5 + u 2*u 5^2*s + u 3*u 5^3*s + u 5) := rfl

theorem XA_L (c : F) (u : V7 F) (s : F) : XA c u s 0 + c * XA c u s 4 = 0 := by
  rw [XA_0, XA_4]; ring

theorem XA_Lz (c : F) (u : V7 F) (s : F) (hu5 : u 5 ≠ 0) :
    Lz c (s * u 5) (-1 / u 5 - s * u 2) (XA c u s) = 0 := by
  have := XA_L c u s
  simp only [Lz]
  have h2 : s * u 5 * XA c u s 2 + (-1 / u 5 - s * u 2) * XA c u s 5 = 0 := by
    rw [XA_2, XA_5]
    field_simp
    ring
  linear_combination this + h2

theorem XA_ne {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu5 : u 5 ≠ 0) :
    c * XA c u s 2 ^ 2 + XA c u s 5 ^ 2 ≠ 0 := by
  have hU : c * u 2 ^ 2 + u 5 ^ 2 ≠ 0 := aniso_ne hc (fun h => hu5 h.2)
  refine aniso_ne hc ?_
  rintro ⟨h2, h5⟩
  rw [XA_2] at h2
  rw [XA_5] at h5
  have hs : s = 0 := by
    have : u 5 ^ 3 * (c * u 2 ^ 2 + u 5 ^ 2) * s = 0 := by linear_combination h5
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (mul_ne_zero (pow_ne_zero 3 hu5) hU)
    · exact h
  subst hs
  have : u 5 * (c * u 2 ^ 2 + u 5 ^ 2) = 0 := by linear_combination h2
  exact mul_ne_zero hu5 hU this

theorem XA_nonzero {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu5 : u 5 ≠ 0) :
    XA c u s ≠ 0 := by
  intro h
  apply XA_ne hc u s hu5
  rw [h]; simp

/-- The denominator `α² + c β²` is nonzero. -/
theorem zA_ne {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu5 : u 5 ≠ 0) :
    (s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2 ≠ 0 := by
  have : (s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2 = c * (1 / u 5 + s * u 2) ^ 2 + (s * u 5) ^ 2 := by
    ring
  rw [this]
  refine aniso_ne hc ?_
  rintro ⟨h1, h2⟩
  have hs : s = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd h hu5
  subst hs
  simp at h1
  exact hu5 h1

/-- The affine identity of step 3 (chart `u₅ ≠ 0`). -/
theorem XA_nu {c : F} (hc : ¬ IsSquare (-c)) (u : V7 F) (s : F) (hu5 : u 5 ≠ 0) :
    nuf c (XA c u s) + (-1 / u 5 - s * u 2) ^ 3 / ((s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2) =
      -(u 2 ^ 3 * u 5 * s + u 2 ^ 2 - u 2 * u 3 * u 5 + u 4 * u 5 ^ 2) / (u 5 * (c * u 2 ^ 2 + u 5 ^ 2)) := by
  have hU : c * u 2 ^ 2 + u 5 ^ 2 ≠ 0 := aniso_ne hc (fun h => hu5 h.2)
  have hZ := zA_ne hc u s hu5
  have hΛ : c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2 ≠ 0 := by
    intro h
    apply hZ
    have : (s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2 =
        (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2) / u 5 ^ 2 := by
      field_simp
      ring
    rw [this, h, zero_div]
  have hD : c * XA c u s 2 ^ 2 + XA c u s 5 ^ 2 =
      u 5 ^ 2 * (c * u 2 ^ 2 + u 5 ^ 2) ^ 2 * (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2) := by
    rw [XA_2, XA_5]; ring
  have hβ : (-1 / u 5 - s * u 2) ^ 3 / ((s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2) =
      -(1 + s * u 2 * u 5) ^ 3 / (u 5 * (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2)) := by
    have e1 : (s * u 5) ^ 2 + c * (-1 / u 5 - s * u 2) ^ 2 =
        (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2) / u 5 ^ 2 := by
      field_simp
      ring
    rw [e1]
    field_simp
    ring
  unfold nuf
  rw [hβ, hD, XA_2, XA_3, XA_4, XA_5]
  have hDne : u 5 ^ 2 * (c * u 2 ^ 2 + u 5 ^ 2) ^ 2 * (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hu5) (pow_ne_zero 2 hU)) hΛ
  have hEne : u 5 * (c * (1 + s * u 2 * u 5) ^ 2 + (s * u 5 ^ 2) ^ 2) ≠ 0 := mul_ne_zero hu5 hΛ
  have hFne : u 5 * (c * u 2 ^ 2 + u 5 ^ 2) ≠ 0 := mul_ne_zero hu5 hU
  rw [div_add_div _ _ hDne hEne, div_eq_div_iff (mul_ne_zero hDne hEne) hFne]
  ring

end BipartiteDD.HexagonD
