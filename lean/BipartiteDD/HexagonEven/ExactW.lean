import BipartiteDD.HexagonEven.Exact

/-! Theorem D (even `q`), step 4: every free point lies on exactly one line of the whisker set `Wset` (mirror of
`HexagonD/FreeLines.lean`, `exists_unique_wline`), by the key identity instead of charts. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon BipartiteDD.HexagonD Module Submodule

variable {F : Type*} [Field F]

/-- `λ₀(x) = x₀ + x₃ + d x₄` (the functional of `Π`). -/
def lam0 (d : F) (x : V7 F) : F := x 0 + x 3 + d * x 4

theorem lam0_smul_add (d a b : F) (x y : V7 F) : lam0 d (a • x + b • y) = a * lam0 d x + b * lam0 d y := by
  simp only [lam0, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `Ψ'(z) = N(z) - Θ (c₀α + c₁β)`, with `N(z) = u₂(u₀ + du₄ + αu₂ + βu₅) + u₂u₄ + u₄u₅ + βu₂²` and
`Θ = du₂² + u₂u₅ + u₅²`. On `A_u = {αu₂ + βu₅ = 1}`, `Ψ'(z) = 0` is the whisker condition. -/
def Psi' (d c0 c1 : F) (u : V7 F) (z : F × F) : F :=
  u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 + u 4 * u 5 + z.2 * u 2 ^ 2 -
    (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) * (c0 * z.1 + c1 * z.2)

theorem Psi'_shift (h2 : (2 : F) = 0) (d c0 c1 : F) (u : V7 F) (z : F × F) (t : F) :
    Psi' d c0 c1 u (z.1 + t * u 5, z.2 + t * u 2) = Psi' d c0 c1 u z - t * Gcub d c0 c1 (u 5) (u 2) := by
  unfold Psi' Gcub
  linear_combination (t * (u 2 ^ 2 * u 5 + u 2 ^ 3)) * h2

theorem A_shift (h2 : (2 : F) = 0) {u : V7 F} {z : F × F} (hz : u 2 * z.1 + u 5 * z.2 = 1) (t : F) :
    u 2 * (z.1 + t * u 5) + u 5 * (z.2 + t * u 2) = 1 := by
  linear_combination hz + (t * u 2 * u 5) * h2

theorem A_diff (h2 : (2 : F) = 0) {u : V7 F} (hu : u 2 ≠ 0 ∨ u 5 ≠ 0) {z z' : F × F}
    (hz : u 2 * z.1 + u 5 * z.2 = 1) (hz' : u 2 * z'.1 + u 5 * z'.2 = 1) :
    ∃ t : F, z' = (z.1 + t * u 5, z.2 + t * u 2) := by
  have hΔ : u 2 * (z'.1 - z.1) + u 5 * (z'.2 - z.2) = 0 := by linear_combination hz' - hz
  by_cases hu2 : u 2 = 0
  · have hu5 : u 5 ≠ 0 := by
      rcases hu with h | h
      · exact absurd hu2 h
      · exact h
    refine ⟨(z'.1 - z.1) / u 5, ?_⟩
    have e1 : z.1 + (z'.1 - z.1) / u 5 * u 5 = z'.1 := by
      rw [div_mul_cancel₀ _ hu5]; ring
    have e2 : u 5 * (z'.2 - z.2) = 0 := by
      rw [hu2] at hΔ; linear_combination hΔ
    have e3 : z'.2 - z.2 = 0 := (mul_eq_zero.1 e2).resolve_left hu5
    have e4 : z.2 + (z'.1 - z.1) / u 5 * u 2 = z'.2 := by
      rw [hu2, mul_zero, add_zero]; linear_combination -e3
    exact Prod.ext e1.symm e4.symm
  · refine ⟨(z'.2 - z.2) / u 2, ?_⟩
    have key1 : z'.1 - z.1 = (z'.2 - z.2) / u 2 * u 5 := by
      rw [div_mul_eq_mul_div, eq_div_iff hu2]
      linear_combination hΔ - (u 5 * (z'.2 - z.2)) * h2
    have e2 : z.2 + (z'.2 - z.2) / u 2 * u 2 = z'.2 := by
      rw [div_mul_cancel₀ _ hu2]; ring
    have e1 : z.1 + (z'.2 - z.2) / u 2 * u 5 = z'.1 := by linear_combination -key1
    exact Prod.ext e1.symm e2.symm

theorem Psi'_unique (h2 : (2 : F) = 0) {d c0 c1 : F} {u : V7 F} (hu : u 2 ≠ 0 ∨ u 5 ≠ 0)
    (hG : Gcub d c0 c1 (u 5) (u 2) ≠ 0) {z z' : F × F}
    (hz : u 2 * z.1 + u 5 * z.2 = 1) (hz' : u 2 * z'.1 + u 5 * z'.2 = 1)
    (h0 : Psi' d c0 c1 u z = 0) (h0' : Psi' d c0 c1 u z' = 0) : z' = z := by
  obtain ⟨t, rfl⟩ := A_diff h2 hu hz hz'
  rw [Psi'_shift h2, h0] at h0'
  have ht : t = 0 := by
    have h3 : t * Gcub d c0 c1 (u 5) (u 2) = 0 := by linear_combination -h0'
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd h hG
  subst ht
  exact Prod.ext (by simp) (by simp)

theorem exists_A_point {u : V7 F} (hu : u 2 ≠ 0 ∨ u 5 ≠ 0) :
    ∃ z : F × F, u 2 * z.1 + u 5 * z.2 = 1 := by
  rcases hu with h | h
  · exact ⟨(1 / u 2, 0), by simp only [mul_zero, add_zero]; exact mul_one_div_cancel h⟩
  · exact ⟨(0, 1 / u 5), by simp only [mul_zero, zero_add]; exact mul_one_div_cancel h⟩

theorem Psi'_exists {d c0 c1 : F} {u : V7 F} (h2 : (2 : F) = 0) (hG : Gcub d c0 c1 (u 5) (u 2) ≠ 0)
    {z : F × F} (hz : u 2 * z.1 + u 5 * z.2 = 1) :
    ∃ z' : F × F, u 2 * z'.1 + u 5 * z'.2 = 1 ∧ Psi' d c0 c1 u z' = 0 := by
  refine ⟨(z.1 + (Psi' d c0 c1 u z / Gcub d c0 c1 (u 5) (u 2)) * u 5,
    z.2 + (Psi' d c0 c1 u z / Gcub d c0 c1 (u 5) (u 2)) * u 2), A_shift h2 hz _, ?_⟩
  rw [Psi'_shift h2, div_mul_cancel₀ _ hG, sub_self]


/-- `λ₀(J_z u) = α(u₂+u₅) + βdu₂` (char `2`). -/
theorem gamma_formula (h2 : (2 : F) = 0) (d : F) (u : V7 F) (z : F × F) :
    lam0 d (JE d z.1 z.2 u) = z.1 * (u 2 + u 5) + z.2 * (d * u 2) := by
  simp [lam0, JE, JA, JB, JC, JD, JF, JG]
  linear_combination (((d + 1) * u 0 + d * z.1 * u 2 + d ^ 2 * u 4 + (z.1 + d * z.2) * u 5) +
    d * (u 0 + (z.1 + z.2) * u 2 + d * u 4 + z.2 * u 5)) * h2

/-- The point `X_z = γ u + J_z u` (`γ = λ₀(J_z u)`), the `Π`-point of the line `⟨u, J_z u⟩`. -/
def Xv (d : F) (u : V7 F) (z : F × F) : V7 F := lam0 d (JE d z.1 z.2 u) • u + JE d z.1 z.2 u

/-- **Key identity along `A_u`** (`Lemma key2` of `evenq.tex`): `ν(X_z) + β³/D₂ = N(z)/Θ`. -/
theorem key_div {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {u : V7 F} {z : F × F}
    (hΘ : d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2 ≠ 0)
    (hz : u 2 * z.1 + u 5 * z.2 = 1) (hu3 : u 3 = u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) :
    nuE d (Xv d u z) + z.2 ^ 3 / (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2) =
      (u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 + u 4 * u 5 + z.2 * u 2 ^ 2) /
        (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) := by
  have hγ := gamma_formula h2 d u z
  unfold Xv
  generalize hg : lam0 d (JE d z.1 z.2 u) = γ at hγ ⊢
  have c2 : (γ • u + JE d z.1 z.2 u) 2 = γ * u 2 + (u 2 + u 5) := by
    simp [JE, JC, JA, JB, JD, JF, JG]
  have c5 : (γ • u + JE d z.1 z.2 u) 5 = γ * u 5 + d * u 2 := by
    simp [JE, JC, JA, JB, JD, JF, JG]
  have c4 : (γ • u + JE d z.1 z.2 u) 4 =
      γ * u 4 + (u 0 + (z.1 + z.2) * u 2 + d * u 4 + z.2 * u 5) := by
    simp [JE, JC, JA, JB, JD, JF, JG]
  have c3 : (γ • u + JE d z.1 z.2 u) 3 = γ * u 3 + ((d + 1) * u 0 + d * z.1 * u 2 + d ^ 2 * u 4 +
      (z.1 + d * z.2) * u 5 + d * (u 0 + (z.1 + z.2) * u 2 + d * u 4 + z.2 * u 5) +
      z.1 * (u 2 + u 5) + z.2 * (d * u 2)) := by
    simp [JE, JC, JA, JB, JD, JF, JG]
  rw [nuE, c2, c3, c4, c5, hu3]
  have hα : z.1 * (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) = d * u 2 + γ * u 5 := by
    linear_combination (d * u 2) * hz - u 5 * hγ - (d * u 2 * z.2 * u 5) * h2
  have hβ : z.2 * (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) = (γ + 1) * u 2 + u 5 := by
    linear_combination (-(u 2 + u 5)) * hz - u 2 * hγ + ((u 2 + u 5) * (u 5 * z.2 - 1)) * h2
  have hK := key_cleared d γ (u 0) (u 2) (u 4) (u 5) z.1 z.2 h2 hΘ hα hβ
  have hden : d * (γ * u 2 + (u 2 + u 5)) ^ 2 + (γ * u 2 + (u 2 + u 5)) * (γ * u 5 + d * u 2) +
      (γ * u 5 + d * u 2) ^ 2 ≠ 0 := by
    have e : d * (γ * u 2 + (u 2 + u 5)) ^ 2 + (γ * u 2 + (u 2 + u 5)) * (γ * u 5 + d * u 2) +
        (γ * u 5 + d * u 2) ^ 2 = (γ ^ 2 + γ + d) * (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) := by
      linear_combination (d * γ * u 2 ^ 2 + 2 * d * γ * u 2 * u 5 + d * u 2 ^ 2 + d * u 2 * u 5) * h2
    rw [e]
    exact mul_ne_zero (hd γ) hΘ
  have hz0 : z ≠ (0, 0) := by
    rintro rfl
    simp at hz
  have hD2 : z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2 ≠ 0 := D2_ne hd hz0
  rw [div_add_div _ _ hden hD2, div_eq_div_iff (mul_ne_zero hden hD2) hΘ]
  linear_combination hK

/-- The whisker condition at `z ∈ A_u`: `ν(X_z) = F(z)` iff `Ψ'(z) = 0`. -/
theorem cond_iff {d c0 c1 : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {u : V7 F} {z : F × F}
    (hΘ : d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2 ≠ 0)
    (hz : u 2 * z.1 + u 5 * z.2 = 1) (hu3 : u 3 = u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) :
    nuE d (Xv d u z) = Fz d c0 c1 z ↔ Psi' d c0 c1 u z = 0 := by
  have hz0 : z ≠ (0, 0) := by
    rintro rfl
    simp at hz
  have hD2 : z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2 ≠ 0 := D2_ne hd hz0
  have hk := key_div hd h2 hΘ hz hu3
  rw [Fz_eq d c0 c1 z hD2]
  have hΘ' : (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) * ((u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 +
      u 4 * u 5 + z.2 * u 2 ^ 2) / (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2)) = u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 +
      u 4 * u 5 + z.2 * u 2 ^ 2 := mul_div_cancel₀ _ hΘ
  constructor
  · intro h
    have h' : (u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 + u 4 * u 5 + z.2 * u 2 ^ 2) /
        (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) = c0 * z.1 + c1 * z.2 := by
      linear_combination -hk + h + (z.2 ^ 3 / (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2)) * h2
    unfold Psi'
    rw [← h']
    linear_combination -hΘ'
  · intro h
    have h' : (u 2 * (u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5) + u 2 * u 4 + u 4 * u 5 + z.2 * u 2 ^ 2) /
        (d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2) = c0 * z.1 + c1 * z.2 := by
      rw [div_eq_iff hΘ]
      unfold Psi' at h
      linear_combination h
    linear_combination hk + h' - (z.2 ^ 3 / (z.1 ^ 2 + z.1 * z.2 + d * z.2 ^ 2)) * h2


theorem u3_of {d : F} {u : V7 F} {z : F × F} (h2 : (2 : F) = 0) (hu1 : lam0 d u = 1)
    (hz : u 2 * z.1 + u 5 * z.2 = 1) : u 3 = u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5 := by
  unfold lam0 at hu1
  linear_combination hu1 - hz - (u 0 + d * u 4) * h2

theorem smul_rep_mem' {p : SPt F} {m : HLine F} {a : F} (ha : a ≠ 0) :
    a • p.1.rep ∈ m.1 ↔ hexInc p m := by
  constructor
  · intro h
    have := m.1.smul_mem a⁻¹ h
    show p.1.rep ∈ m.1
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro h
    exact m.1.smul_mem a h

/-- A nonzero singular vector with `x₂ = x₅ = 0` lies on a line meeting `v`. -/
theorem exists_line_meets_vStd' {x : V7 F} (hx0 : x ≠ 0) (hQ : Qf x = 0) (h2 : x 2 = 0) (h5 : x 5 = 0) :
    ∃ M : HLine F, x ∈ M.1 ∧ ∃ r : SPt F, hexInc r (vStd' : HLine F) ∧ hexInc r M := by
  obtain ⟨a, b, hab, hc1, hc2⟩ : ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a * x 0 = b * x 3 ∧ b * x 4 = a * x 3 := by
    by_cases h : x 3 = 0 ∧ x 0 = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h.2], by simp [h.1]⟩
    · refine ⟨x 3, x 0, ?_, by ring, ?_⟩
      · by_contra hh
        push Not at hh
        exact h hh
      · simp only [Qf] at hQ
        rw [h2, h5] at hQ
        linear_combination hQ
  let r' : V7 F := ![0, a, 0, 0, 0, 0, b]
  have hr'0 : r' ≠ 0 := by
    intro h
    have h1 := congr_fun h 1
    have h6 := congr_fun h 6
    simp [r'] at h1 h6
    rcases hab with h | h
    · exact h h1
    · exact h h6
  have hr'Q : Qf r' = 0 := by simp [Qf, r']
  have hr'v : r' ∈ (vStd' : HLine F).1 := mem_vStd'.2 (by simp [r'])
  have hpair : IsHPair x r' := by
    refine ⟨hQ, hr'Q, ?_, ?_⟩
    · simp [Bf, r', h2, h5]
    · simp only [Tits, pl, r']
      simp [h2, h5]
      refine ⟨?_, ?_⟩
      · linear_combination hc1
      · linear_combination hc2
  obtain ⟨M, hxM, hr'M⟩ := exists_hline_of_isHPair_even hx0 hpair
  exact ⟨M, hxM, sptOf r' hr'0 hr'Q, sptOf_mem.2 hr'v, sptOf_mem.2 hr'M⟩

/-- **Step 4 (even `q`)**: every free point lies on exactly one line of the whisker set. -/
theorem exists_unique_wline_even [Fintype F] {d c0 c1 : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0)
    (h2 : (2 : F) = 0) (hG : GoodCubicE d c0 c1) {p : SPt F} (hp : ¬ OnPiE d p)
    (hfree : ¬ ∃ M : HLine F, hexInc p M ∧ Meets vStd' M) :
    ∃! m : HLine F, m ∈ Wset d c0 c1 ∧ hexInc p m := by
  have hL : p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 ≠ 0 := hp
  set l := p.1.rep 0 + p.1.rep 3 + d * p.1.rep 4 with hl
  set u : V7 F := l⁻¹ • p.1.rep with hu
  have hQu : Qf u = 0 := by rw [hu, Qf_smul, p.2, mul_zero]
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hL) p.1.rep_nonzero
  have hu1 : lam0 d u = 1 := by
    have : lam0 d u = l⁻¹ * l := by
      simp only [hu, lam0, Pi.smul_apply, smul_eq_mul, hl]
      ring
    rw [this, inv_mul_cancel₀ hL]
  have hmem : ∀ m : HLine F, u ∈ m.1 ↔ hexInc p m := fun m => smul_rep_mem' (inv_ne_zero hL)
  have hu25 : u 2 ≠ 0 ∨ u 5 ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨M, hxM, r, hr1, hr2⟩ := exists_line_meets_vStd' hu0 hQu h.1 h.2
    exact hfree ⟨M, (hmem M).1 hxM, r, hr1, hr2⟩
  have hΘ : d * u 2 ^ 2 + u 2 * u 5 + u 5 ^ 2 ≠ 0 := by
    have hne : (u 5, u 2) ≠ (0, 0) := by
      intro h
      rcases hu25 with h' | h'
      · exact h' (Prod.ext_iff.1 h).2
      · exact h' (Prod.ext_iff.1 h).1
    have := D2_ne hd hne
    intro h
    apply this
    linear_combination h
  have hG' : Gcub d c0 c1 (u 5) (u 2) ≠ 0 := by
    have hne : ¬ (u 5 = 0 ∧ u 2 = 0) := by
      rintro ⟨h5, h2'⟩
      rcases hu25 with h' | h'
      · exact h' h2'
      · exact h' h5
    exact hG _ _ hne
  have hA : ∀ z : F × F, u 2 * z.1 + u 5 * z.2 = 1 → InPiZE d z.1 z.2 u := by
    intro z hz
    unfold InPiZE
    unfold lam0 at hu1
    linear_combination hu1 + hz + h2
  have hu3 : ∀ z : F × F, u 2 * z.1 + u 5 * z.2 = 1 → u 3 = u 0 + d * u 4 + z.1 * u 2 + z.2 * u 5 :=
    fun z hz => u3_of h2 hu1 hz
  -- existence
  obtain ⟨z0, hz0⟩ := exists_A_point hu25
  obtain ⟨zs, hzs, hPs⟩ := Psi'_exists (d := d) (c0 := c0) (c1 := c1) h2 hG' hz0
  obtain ⟨Ws, hWsspan, hWsPi⟩ := exists_hline_JE hd h2 hu0 hQu (hA zs hzs)
  have huW : u ∈ Ws.1 := by rw [hWsspan]; exact subset_span (by simp)
  have hXmem : Xv d u zs ∈ Ws.1 := by
    rw [hWsspan]
    exact Submodule.mem_span_pair.2 ⟨lam0 d (JE d zs.1 zs.2 u), 1, by simp [Xv]⟩
  have hXne : Xv d u zs ≠ 0 := by
    intro h
    apply JE_not_mem_span hd h2 hu0 (hA zs hzs)
    rw [Submodule.mem_span_singleton]
    unfold Xv at h
    have hJ : JE d zs.1 zs.2 u = -(lam0 d (JE d zs.1 zs.2 u) • u) :=
      eq_neg_iff_add_eq_zero.2 (by rw [add_comm]; exact h)
    exact ⟨-lam0 d (JE d zs.1 zs.2 u), by rw [neg_smul, ← hJ]⟩
  have hXlam : lam0 d (Xv d u zs) = 0 := by
    have e := lam0_smul_add d (lam0 d (JE d zs.1 zs.2 u)) 1 u (JE d zs.1 zs.2 u)
    rw [one_smul, hu1] at e
    unfold Xv
    rw [e]
    linear_combination (lam0 d (JE d zs.1 zs.2 u)) * h2
  have hnu : nuE d (Xv d u zs) = Fz d c0 c1 zs := (cond_iff hd h2 hΘ hzs (hu3 zs hzs)).2 hPs
  have hWs : Ws ∈ Wset d c0 c1 := by
    refine ⟨?_, zs, ?_, fun x hx => hWsPi x hx, Xv d u zs, hXmem, hXne, hXlam, hnu⟩
    · intro h
      have h1 : lam0 d u = 0 := vStd'_Pi d u (h ▸ huW)
      rw [hu1] at h1
      exact one_ne_zero h1
    · intro h
      rw [h] at hzs
      simp at hzs
  refine ⟨Ws, ⟨hWs, (hmem Ws).1 huW⟩, ?_⟩
  rintro m ⟨hm, hpm⟩
  have hum : u ∈ m.1 := (hmem m).2 hpm
  obtain ⟨-, z, hz0', hzPi, x0, hx0m, hx0ne, hx0Pi, hnu'⟩ := hm
  have hzA : u 2 * z.1 + u 5 * z.2 = 1 := by
    have hzPi' : u 0 + u 3 + d * u 4 + z.1 * u 2 + z.2 * u 5 = 0 := hzPi u hum
    unfold lam0 at hu1
    linear_combination hzPi' - hu1 - h2
  obtain ⟨Wz, hWzspan, hWzPi⟩ := exists_hline_JE hd h2 hu0 hQu (hA z hzA)
  have hmz : m = Wz := by
    have hyuW : u ∈ Wz.1 := by rw [hWzspan]; exact subset_span (by simp)
    exact slineZE_unique hd h2 hu0 hQu (by have := hA z hzA; unfold InPiZE at this; exact this)
      hzPi hWzPi hum hyuW
  have hx0W : x0 ∈ span F {u, JE d z.1 z.2 u} := by
    rw [← hWzspan, ← hmz]; exact hx0m
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hx0W
  have hx0Pi' : lam0 d x0 = 0 := hx0Pi
  have hlin : a * 1 + b * lam0 d (JE d z.1 z.2 u) = 0 := by
    have e := lam0_smul_add d a b u (JE d z.1 z.2 u)
    rw [hab, hx0Pi', hu1] at e
    linear_combination -e
  have ha' : a = b * lam0 d (JE d z.1 z.2 u) := by
    linear_combination hlin - (b * lam0 d (JE d z.1 z.2 u)) * h2
  have hb : b ≠ 0 := by
    intro hb
    apply hx0ne
    have ha0 : a = 0 := by rw [ha', hb, zero_mul]
    rw [← hab, ha0, hb, zero_smul, zero_smul, add_zero]
  have hx : x0 = b • Xv d u z := by
    rw [← hab, Xv, smul_add, ha', mul_smul]
  rw [hx, nuE_smul d hb] at hnu'
  have hPz : Psi' d c0 c1 u z = 0 := (cond_iff hd h2 hΘ hzA (hu3 z hzA)).1 hnu'
  have hzeq : zs = z := Psi'_unique h2 hu25 hG' hzA hzs hPz hPs
  have hmz' : ∀ x ∈ m.1, InPiZE d zs.1 zs.2 x := by
    rw [hzeq]; exact hzPi
  exact slineZE_unique (α := zs.1) (β := zs.2) hd h2 hu0 hQu (hA zs hzs) hmz' hWsPi hum huW

end BipartiteDD.HexagonEven
