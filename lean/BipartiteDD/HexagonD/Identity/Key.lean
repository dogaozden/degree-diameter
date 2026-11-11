import BipartiteDD.HexagonD.Identity.Nu

/-! Theorem D, algebraic core, part 4: the key identity.

Let `p` be a point with `p₀ + c p₄ = 1` (so `λ(p) = 1`, where `λ(y) = y₀ + c y₄`) and let `z = (α, β)` satisfy
`α p₂ + β p₅ = -1`, i.e. `p ∈ Π_z`. Put `Θ = c p₂² + p₅²` and `γ = -α p₅ + c β p₂`. Then `J_z p` has `λ(J_z p) = γ`,
and the point `X(z) = γ p - J_z p` lies on `Π` (it is the point of `⟨p, J_z p⟩` on `Π`). The key identity says

  `ν(X(z)) + β³/(α² + c β²) = (p₂p₃ - p₄p₅ + β p₂²) / Θ`,

which is affine in `β` along the constraint line; moving `z` by `(p₅, -p₂)` (so `β` changes by `-p₂`) changes the
right-hand side by `-p₂³ / Θ`. -/

namespace BipartiteDD.HexagonD.Identity

open BipartiteDD.Hexagon Module

variable {F : Type*} [Field F]

/-- `Φ_p(z) = ν(γ p - J_z p) + β³ / (α² + c β²)`, with `γ = -α p₅ + c β p₂`. -/
def PhiP (c : F) (p : V7 F) (α β : F) : F :=
  nu c ((-α * p 5 + c * β * p 2) • p - Jz c α β p) + β ^ 3 / (α ^ 2 + c * β ^ 2)

/-- The point `X(z) = γ p - J_z p` lies on `Π` when `λ(p) = 1` (`γ = -α p₅ + c β p₂`). -/
theorem Xpt_mem_Pi {c α β γ : F} {p : V7 F} (hp0 : p 0 + c * p 4 = 1)
    (hγ : γ = -α * p 5 + c * β * p 2) : (γ • p - Jz c α β p) 0 + c * (γ • p - Jz c α β p) 4 = 0 := by
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Jz_0, Jz_4]
  linear_combination γ * hp0 + hγ

/-- **Key identity.** -/
theorem key_identity {c α β : F} (hc : ¬ IsSquare (-c)) {p : V7 F}
    (hz : α * p 2 + β * p 5 = -1) :
    PhiP c p α β = (p 2 * p 3 - p 4 * p 5 + β * p 2 ^ 2) / (c * p 2 ^ 2 + p 5 ^ 2) := by
  unfold PhiP
  obtain ⟨γ, hγ⟩ : ∃ γ : F, γ = -α * p 5 + c * β * p 2 := ⟨_, rfl⟩
  rw [← hγ]
  -- `Θ ≠ 0`: otherwise `-c` is a square, since `(p₂, p₅) ≠ 0`
  have hΘ : c * p 2 ^ 2 + p 5 ^ 2 ≠ 0 := by
    intro h
    rcases eq_or_ne (p 2) 0 with h2 | h2
    · have h5 : p 5 = 0 := by
        rw [h2] at h
        simpa using h
      rw [h2, h5] at hz
      simp at hz
    · apply hc
      refine ⟨p 5 / p 2, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero h2 h2)]
      linear_combination -h
  have hγ2 : γ ^ 2 + c ≠ 0 := by
    intro h
    exact hc ⟨γ, by linear_combination -h⟩
  -- `X(z)`-independent facts: `α Θ` and `β Θ` in terms of `γ`
  have hA : α * (c * p 2 ^ 2 + p 5 ^ 2) = -(c * p 2 + γ * p 5) := by
    linear_combination (c * p 2) * hz + p 5 * hγ
  have hB : β * (c * p 2 ^ 2 + p 5 ^ 2) = γ * p 2 - p 5 := by
    linear_combination p 5 * hz - p 2 * hγ
  have hAB0 : (c * p 2 ^ 2 + p 5 ^ 2) *
      ((α ^ 2 + c * β ^ 2) * (c * p 2 ^ 2 + p 5 ^ 2) - (γ ^ 2 + c)) = 0 := by
    linear_combination (α * (c * p 2 ^ 2 + p 5 ^ 2) - c * p 2 - γ * p 5) * hA +
      c * (β * (c * p 2 ^ 2 + p 5 ^ 2) + γ * p 2 - p 5) * hB
  have hAB : α ^ 2 + c * β ^ 2 = (γ ^ 2 + c) / (c * p 2 ^ 2 + p 5 ^ 2) := by
    rw [eq_div_iff hΘ]
    exact sub_eq_zero.1 ((mul_eq_zero.1 hAB0).resolve_left hΘ)
  have hB2 : β ^ 3 * (c * p 2 ^ 2 + p 5 ^ 2) ^ 2 = β * (γ * p 2 - p 5) ^ 2 := by
    linear_combination (β * (β * (c * p 2 ^ 2 + p 5 ^ 2) + γ * p 2 - p 5)) * hB
  have hnum : num (γ • p - Jz c α β p) =
      (γ ^ 2 + c) * (p 2 * p 3 - p 4 * p 5) + β * (2 * γ * p 2 * p 5 + c * p 2 ^ 2 - p 5 ^ 2) := by
    unfold num
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Jz_2, Jz_3, Jz_4, Jz_5]
    ring
  have hden : den c (γ • p - Jz c α β p) = (γ ^ 2 + c) * (c * p 2 ^ 2 + p 5 ^ 2) := by
    unfold den
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Jz_2, Jz_5]
    ring
  unfold nu
  rw [hnum, hden, hAB, div_div_eq_mul_div, div_add_div _ _ (mul_ne_zero hγ2 hΘ) hγ2,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hγ2 hΘ) hγ2) hΘ]
  linear_combination ((γ ^ 2 + c) * (c * p 2 ^ 2 + p 5 ^ 2)) * hB2

/-- The increment of `Φ_p` along the direction `(p₅, -p₂)` of `A_p`: it is `-p₂³ / Θ`. -/
theorem key_increment {c α β : F} (hc : ¬ IsSquare (-c)) {p : V7 F}
    (hz : α * p 2 + β * p 5 = -1) :
    PhiP c p (α + p 5) (β - p 2) - PhiP c p α β = -p 2 ^ 3 / (c * p 2 ^ 2 + p 5 ^ 2) := by
  have hz' : (α + p 5) * p 2 + (β - p 2) * p 5 = -1 := by
    linear_combination hz
  rw [key_identity hc hz', key_identity hc hz, div_sub_div_same]
  congr 1
  ring

end BipartiteDD.HexagonD.Identity
