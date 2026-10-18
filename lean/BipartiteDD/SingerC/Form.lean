import BipartiteDD.SingerC.Core

/-! Part (a) of Proposition C: the form `B(x,y) = Tr_{K/F}(d x y^{q²})` is F-bilinear and
alternating, and multiplication by `g^{q+1}` scales it. Traces are explicit Frobenius sums:
`tr4 z = z + z^q + z^{q²} + z^{q³}` (K to F) and `tr2 w = w + w^q` (L to F). -/

namespace BipartiteDD.SingerC

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- The trace from `K` to `F`. -/
def tr4 (z : K) : K := z + z ^ S.q + z ^ (S.q ^ 2) + z ^ (S.q ^ 3)

/-- The trace from `L` to `F`. -/
def tr2 (w : K) : K := w + w ^ S.q

/-- The form `B(x, y) = Tr_{K/F}(d · x · y^{q²})`. -/
def B (x y : K) : K := S.tr4 (S.d * x * y ^ (S.q ^ 2))

theorem add_pow_q1 (x y : K) : (x + y) ^ S.q = x ^ S.q + y ^ S.q := by
  simpa using S.add_pow_q 1 x y

theorem add_pow_q2 (x y : K) : (x + y) ^ S.q ^ 2 = x ^ S.q ^ 2 + y ^ S.q ^ 2 :=
  S.add_pow_q 2 x y

theorem add_pow_q3 (x y : K) : (x + y) ^ S.q ^ 3 = x ^ S.q ^ 3 + y ^ S.q ^ 3 :=
  S.add_pow_q 3 x y

theorem neg_pow_q (w : K) : (-w) ^ S.q = -w ^ S.q := S.q_odd.neg_pow w

theorem tr4_add (x y : K) : S.tr4 (x + y) = S.tr4 x + S.tr4 y := by
  unfold tr4
  rw [add_pow_q1, add_pow_q2, add_pow_q3]
  ring

theorem tr2_add (x y : K) : S.tr2 (x + y) = S.tr2 x + S.tr2 y := by
  unfold tr2
  rw [add_pow_q1]
  ring

theorem tr2_neg (w : K) : S.tr2 (-w) = -S.tr2 w := by
  unfold tr2
  rw [neg_pow_q]
  ring

theorem pow_pow_q (z : K) (a b : ℕ) : (z ^ S.q ^ a) ^ S.q ^ b = z ^ S.q ^ (a + b) := by
  rw [← pow_mul, ← pow_add]

theorem tr4_smul (c : K) (hc : c ∈ S.F) (z : K) : S.tr4 (c * z) = c * S.tr4 z := by
  have hc1 : c ^ S.q = c := S.mem_F.mp hc
  have hc2 : c ^ S.q ^ 2 = c := S.pow_q_pow_of_pow_q hc1 2
  have hc3 : c ^ S.q ^ 3 = c := S.pow_q_pow_of_pow_q hc1 3
  unfold tr4
  rw [mul_pow, mul_pow, mul_pow, hc1, hc2, hc3]
  ring

theorem tr2_smul (c : K) (hc : c ∈ S.F) (w : K) : S.tr2 (c * w) = c * S.tr2 w := by
  have hc' : c ^ S.q = c := S.mem_F.mp hc
  unfold tr2
  rw [mul_pow, hc']
  ring

theorem tr4_eq_tr2 (z : K) : S.tr4 z = S.tr2 (z + z ^ (S.q ^ 2)) := by
  unfold tr4 tr2
  rw [add_pow_q1]
  ring

/-- The conjugate `z ↦ z^{q²}` preserves the trace. -/
theorem tr4_conj (z : K) : S.tr4 (z ^ (S.q ^ 2)) = S.tr4 z := by
  unfold tr4
  have e1 : (z ^ S.q ^ 2) ^ S.q = z ^ S.q ^ 3 := by
    rw [← pow_mul, ← pow_succ]
  have e2 : (z ^ S.q ^ 2) ^ S.q ^ 2 = z := by
    rw [S.pow_pow_q z 2 2, show 2 + 2 = 4 by rfl, S.pow_card]
  have e3 : (z ^ S.q ^ 2) ^ S.q ^ 3 = z ^ S.q := by
    rw [S.pow_pow_q z 2 3, show 2 + 3 = 4 + 1 by rfl, pow_succ, pow_mul, S.pow_card]
  rw [e1, e2, e3]
  ring

theorem tr4_eq_zero_of_conj_neg (z : K) (hz : z ^ (S.q ^ 2) = -z) : S.tr4 z = 0 := by
  rw [S.tr4_eq_tr2, hz, add_neg_cancel]
  unfold tr2
  rw [zero_pow S.q_odd.pos.ne', add_zero]

theorem B_eq_tr2 (x y : K) : S.B x y = S.tr2 (S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y)) := by
  unfold B
  rw [S.tr4_eq_tr2]
  congr 1
  have hconj : (S.d * x * y ^ (S.q ^ 2)) ^ (S.q ^ 2) = -(S.d * x ^ (S.q ^ 2) * y) := by
    rw [mul_pow, mul_pow, S.d_pow_q_sq, S.pow_pow_q y 2 2, show 2 + 2 = 4 by rfl, S.pow_card]
    ring
  rw [hconj]
  ring

theorem B_add_left (x x' y : K) : S.B (x + x') y = S.B x y + S.B x' y := by
  unfold B
  rw [show S.d * (x + x') * y ^ (S.q ^ 2) = S.d * x * y ^ (S.q ^ 2) + S.d * x' * y ^ (S.q ^ 2) by ring,
    S.tr4_add]

theorem B_add_right (x y y' : K) : S.B x (y + y') = S.B x y + S.B x y' := by
  unfold B
  rw [add_pow_q2, show S.d * x * (y ^ S.q ^ 2 + y' ^ S.q ^ 2) = S.d * x * y ^ S.q ^ 2 + S.d * x * y' ^ S.q ^ 2 by ring,
    S.tr4_add]

theorem B_smul_left (c : K) (hc : c ∈ S.F) (x y : K) : S.B (c * x) y = c * S.B x y := by
  unfold B
  rw [show S.d * (c * x) * y ^ (S.q ^ 2) = c * (S.d * x * y ^ (S.q ^ 2)) by ring, S.tr4_smul c hc]

theorem B_smul_right (c : K) (hc : c ∈ S.F) (x y : K) : S.B x (c * y) = c * S.B x y := by
  unfold B
  have hc2 : c ^ S.q ^ 2 = c := S.pow_q_pow_of_pow_q (S.mem_F.mp hc) 2
  rw [show S.d * x * (c * y) ^ (S.q ^ 2) = c * (S.d * x * y ^ (S.q ^ 2)) by
    rw [mul_pow, hc2]; ring, S.tr4_smul c hc]

/-- Alternating: the form is antisymmetric, hence `B x x = 0` in characteristic not 2. -/
theorem B_antisymm (x y : K) : S.B x y = -S.B y x := by
  rw [S.B_eq_tr2, S.B_eq_tr2, ← S.tr2_neg]
  congr 1
  ring

theorem B_self (x : K) : S.B x x = 0 := by
  have h := S.B_antisymm x x
  have h2 : (2 : K) ≠ 0 := by
    intro h0
    have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    rw [CharP.cast_eq_zero_iff K p] at h1
    have hle := Nat.le_of_dvd (by norm_num) h1
    have hp2 := (Fact.out : p.Prime).two_le
    obtain ⟨k, hk⟩ := S.odd_p
    omega
  have h3 : 2 * S.B x x = 0 := by linear_combination h
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 h2
  · exact h4

/-- `λ = g^{q+1}` and `c = λ^{q²+1} = g^{(q+1)(q²+1)} ∈ F`. -/
theorem scale_mem_F : (S.g ^ (S.q + 1)) ^ (S.q ^ 2 + 1) ∈ S.F := by
  rw [mem_F, S.q_pow_eq]
  have h1 : ((S.g ^ (S.q + 1)) ^ (S.q ^ 2 + 1)) ^ (S.q - 1) = 1 := by
    rw [← pow_mul, ← pow_mul]
    have hq : (S.q + 1) * ((S.q ^ 2 + 1) * (S.q - 1)) = Fintype.card K - 1 := by
      rw [S.card_eq', S.q_sq_sub_one_mul']
      ring
    rw [hq]
    exact S.g_pow_N
  rw [h1, one_mul]

theorem scale_ne_zero : (S.g ^ (S.q + 1)) ^ (S.q ^ 2 + 1) ≠ 0 :=
  pow_ne_zero _ (pow_ne_zero _ S.g_ne_zero)

/-- Multiplication by `λ = g^{q+1}` scales the form by `λ^{q²+1} ∈ F`. -/
theorem B_scale (x y : K) :
    S.B (S.g ^ (S.q + 1) * x) (S.g ^ (S.q + 1) * y)
      = (S.g ^ (S.q + 1)) ^ (S.q ^ 2 + 1) * S.B x y := by
  unfold B
  rw [mul_pow, ← S.tr4_smul _ S.scale_mem_F]
  congr 1
  rw [pow_succ]
  ring

open Polynomial in
/-- A nonzero `c` makes `z ↦ Tr(c z)` nonzero on `K`: the polynomial has degree `< |K|`. -/
theorem tr4_mul_exists_ne_zero {c : K} (hc : c ≠ 0) : ∃ z : K, S.tr4 (c * z) ≠ 0 := by
  by_contra hall
  push_neg at hall
  set P : K[X] := C c * X ^ 1 + C (c ^ S.q) * X ^ S.q + C (c ^ S.q ^ 2) * X ^ S.q ^ 2
    + C (c ^ S.q ^ 3) * X ^ S.q ^ 3 with hP
  have heval : ∀ z : K, P.eval z = 0 := by
    intro z
    have h := hall z
    unfold tr4 at h
    simp only [mul_pow] at h
    rw [hP]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, pow_one]
    linear_combination h
  have hq1 : 1 ≤ S.q := S.q_odd.pos
  have hq3 : 1 ≤ S.q ^ 3 := Nat.one_le_pow _ _ hq1
  have term : ∀ (a : K) (n : ℕ), n ≤ S.q ^ 3 → (C a * X ^ n).natDegree ≤ S.q ^ 3 :=
    fun a n hn => (natDegree_C_mul_X_pow_le a n).trans hn
  have hdeg : P.natDegree ≤ S.q ^ 3 := by
    rw [hP]
    refine (natDegree_add_le _ _).trans (max_le ((natDegree_add_le _ _).trans (max_le
      ((natDegree_add_le _ _).trans (max_le ?_ ?_)) ?_)) ?_)
    · exact term _ _ hq3
    · exact term _ _ (Nat.le_self_pow (by norm_num) S.q)
    · exact term _ _ (Nat.pow_le_pow_right hq1 (by norm_num))
    · exact term _ _ le_rfl
  have hK : P.natDegree < Fintype.card K := by
    rw [S.card_eq']
    have : S.q ^ 3 < S.q ^ 4 := Nat.pow_lt_pow_right (by have := S.q_ge_three; omega) (by norm_num)
    omega
  have hP0 : P = 0 := by
    apply eq_zero_of_forall_eval_zero_of_natDegree_lt_card P heval
    simpa [Nat.card_eq_fintype_card] using hK
  have hc1 : P.coeff 1 = c := by
    have h1 : (1 : ℕ) ≠ S.q := by have := S.q_ge_three; omega
    have h2 : (1 : ℕ) ≠ S.q ^ 2 := by
      have := S.q_ge_three
      have : S.q ≤ S.q ^ 2 := Nat.le_self_pow (by norm_num) S.q
      omega
    have h3 : (1 : ℕ) ≠ S.q ^ 3 := by
      have := S.q_ge_three
      have : S.q ≤ S.q ^ 3 := Nat.le_self_pow (by norm_num) S.q
      omega
    rw [hP]
    simp only [coeff_add, coeff_C_mul_X_pow, h1, h2, h3, ↓reduceIte, add_zero]
  rw [hP0, coeff_zero] at hc1
  exact hc hc1.symm

/-- Nondegeneracy of `B`: for `x ≠ 0` some `y` has `B(x, y) ≠ 0`. -/
theorem B_nondeg {x : K} (hx : x ≠ 0) : ∃ y : K, S.B x y ≠ 0 := by
  have hd : S.d ≠ 0 := pow_ne_zero _ S.g_ne_zero
  obtain ⟨z, hz⟩ := S.tr4_mul_exists_ne_zero (mul_ne_zero hd hx)
  refine ⟨z ^ (S.q ^ 2), ?_⟩
  have hzz : (z ^ S.q ^ 2) ^ S.q ^ 2 = z := by
    rw [← pow_mul, show S.q ^ 2 * S.q ^ 2 = S.q ^ 4 by ring, S.pow_card]
  unfold B
  rw [hzz]
  exact hz

end Setting

end BipartiteDD.SingerC
