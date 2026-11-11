import BipartiteDD.HexagonD.Identity.Line

/-! Theorem D, algebraic core, part 3: the ratio `ν = N / D` is constant on each S-line.

`N(y) = y₂y₃ - y₄y₅` and `D(y) = c y₂² + y₅²`. For `J = J_0` (the case `z = 0`):
`N(J x) = c N(x)`, `D(J x) = c D(x)`, and the polar forms of `N` and `D` vanish on `(x, J x)`. Hence
`N(a x + b J x) = (a² + c b²) N(x)` and `D(a x + b J x) = (a² + c b²) D(x)`, so `ν` is unchanged when `(a, b) ≠ 0`
(`a² + c b² ≠ 0` since `-c` is a non-square). Every S-line through a nonzero point `y` is `⟨y, J y⟩`
(uniqueness of the S-line through a singular point), so `ν` is constant on each S-line (`nu_eq_of_mem_sline`). -/

namespace BipartiteDD.HexagonD.Identity

open BipartiteDD.Hexagon BipartiteDD.HexagonD Module Submodule

variable {F : Type*} [Field F]

/-- `N(y) = y₂ y₃ - y₄ y₅`. -/
def num (y : V7 F) : F := y 2 * y 3 - y 4 * y 5

/-- `D(y) = c y₂² + y₅²`. -/
def den (c : F) (y : V7 F) : F := c * y 2 ^ 2 + y 5 ^ 2

/-- `ν = N / D`. -/
def nu (c : F) (y : V7 F) : F := num y / den c y

theorem num_Jz0 (c : F) (x : V7 F) : num (Jz c 0 0 x) = c * num x := by
  unfold num
  simp only [Jz_2, Jz_3, Jz_4, Jz_5]
  ring

theorem den_Jz0 (c : F) (x : V7 F) : den c (Jz c 0 0 x) = c * den c x := by
  unfold den
  simp only [Jz_2, Jz_5]
  ring

/-- The polar form of `N` vanishes on `(x, J_0 x)`. -/
theorem num_polar (c : F) (x : V7 F) : num (x + Jz c 0 0 x) - num x - num (Jz c 0 0 x) = 0 := by
  unfold num
  simp only [Pi.add_apply, Jz_2, Jz_3, Jz_4, Jz_5]
  ring

/-- The polar form of `D` vanishes on `(x, J_0 x)`. -/
theorem den_polar (c : F) (x : V7 F) :
    den c (x + Jz c 0 0 x) - den c x - den c (Jz c 0 0 x) = 0 := by
  unfold den
  simp only [Pi.add_apply, Jz_2, Jz_5]
  ring

theorem num_comb (c a b : F) (x : V7 F) :
    num (a • x + b • Jz c 0 0 x) = (a ^ 2 + c * b ^ 2) * num x := by
  unfold num
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jz_2, Jz_3, Jz_4, Jz_5]
  ring

theorem den_comb (c a b : F) (x : V7 F) :
    den c (a • x + b • Jz c 0 0 x) = (a ^ 2 + c * b ^ 2) * den c x := by
  unfold den
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Jz_2, Jz_5]
  ring

theorem nu_comb (c a b : F) (x : V7 F) (hk : a ^ 2 + c * b ^ 2 ≠ 0) :
    nu c (a • x + b • Jz c 0 0 x) = nu c x := by
  unfold nu
  rw [num_comb, den_comb, mul_div_mul_left _ _ hk]

/-- For `(a, b) ≠ 0` and `-c` a non-square, `a² + c b² ≠ 0`. -/
theorem sq_add_mul_ne_zero {c : F} (hc : ¬ IsSquare (-c)) {a b : F} (h : a ≠ 0 ∨ b ≠ 0) :
    a ^ 2 + c * b ^ 2 ≠ 0 := by
  intro h0
  by_cases hb : b = 0
  · have ha : a ≠ 0 := h.resolve_right (not_not.2 hb)
    apply ha
    have h2 : a ^ 2 = 0 := by
      rw [hb] at h0
      simpa using h0
    exact (pow_eq_zero_iff two_ne_zero).1 h2
  · refine hc ⟨a / b, ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb hb)]
    linear_combination -h0

/-- `ν` is constant on each S-line: for nonzero `y, w` on an S-line `s`, `ν(w) = ν(y)`. -/
theorem nu_eq_of_mem_sline [NeZero (2 : F)] {c : F} (hc : ¬ IsSquare (-c)) {s : SLine c} {y w : V7 F}
    (hy : y ∈ s.1.1) (hy0 : y ≠ 0) (hw : w ∈ s.1.1) (hw0 : w ≠ 0) : nu c w = nu c y := by
  have hQy : Qf y = 0 := (s.1.2.2 y hy y hy).1
  have hyL : y 0 + c * y 4 = 0 := s.2 y hy
  have hyPz : InPiz c 0 0 y := by
    unfold InPiz
    linear_combination hyL
  -- the S-line `⟨y, J_0 y⟩` through `y`
  let M : HLine F := hlineOf hy0 (isHPair_Jz hyPz hQy) (Jz_not_mem_span hc hy0 hyPz)
  have hM : InPi c M := fun v hv => by
    have h := span_inPiz hyPz hv
    unfold InPiz at h
    linear_combination h
  let sM : SLine c := ⟨M, hM⟩
  have hyM : y ∈ sM.1.1 := by
    show y ∈ span F {y, Jz c 0 0 y}
    exact subset_span (by simp)
  have heq : s = sM := sline_unique hc hy0 hQy hyL hy hyM
  have hs : s.1.1 = span F {y, Jz c 0 0 y} := by
    rw [heq]
    rfl
  rw [hs] at hw
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw0 (by simp [hne.1, hne.2])
  exact nu_comb c a b y (sq_add_mul_ne_zero hc hab)

end BipartiteDD.HexagonD.Identity
