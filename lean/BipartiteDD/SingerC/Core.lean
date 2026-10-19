import BipartiteDD.SingerC.Setup

/-! Basic arithmetic for Proposition C: the fields `F = GF(q)`, `L = GF(q²)` inside
`K = GF(q⁴)`, the elements `d`, `h`, `ω` and the Frobenius identities used later. -/

namespace BipartiteDD.SingerC

open Finset

/-- The data of Proposition C: a finite field `K` of characteristic `p` with `|K| = (p ^ e) ^ 4`
(so `q = p ^ e`), `p` odd, and a generator `g` of `Kˣ`. -/
structure Setting (K : Type*) [Field K] [Fintype K] (p : ℕ) [Fact p.Prime] [CharP K p] where
  e : ℕ
  odd_p : Odd p
  card_eq : Fintype.card K = (p ^ e) ^ 4
  g : K
  orderOf_g : orderOf g = Fintype.card K - 1

/-- A square root of `-1`-type statement: if `x ^ (2k) = 1` and `x ^ k ≠ 1` then `x ^ k = -1`. -/
theorem pow_eq_neg_one_of_sq {K : Type*} [Field K] {x : K} {k : ℕ} (h1 : x ^ (2 * k) = 1) (h2 : x ^ k ≠ 1) :
    x ^ k = -1 := by
  have h3 : x ^ k * x ^ k = 1 := by rw [← pow_add, ← two_mul]; exact h1
  rcases mul_self_eq_one_iff.mp h3 with h | h
  · exact absurd h h2
  · exact h

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- `q = p ^ e`, the order of the base field `F`. -/
def q : ℕ := p ^ S.e

/-- `F = GF(q)`, the fixed field of `x ↦ x ^ q`. -/
def F : Subfield K := fixSub S.odd_p S.e

/-- `L = GF(q²)`, the fixed field of `x ↦ x ^ (q ^ 2)`. -/
def L : Subfield K := fixSub S.odd_p (2 * S.e)

/-- `d = g ^ ((q² + 1) / 2)`. -/
def d : K := S.g ^ ((S.q ^ 2 + 1) / 2)

/-- `h = g ^ (q² + 1)`, a generator of `Lˣ`. -/
def h : K := S.g ^ (S.q ^ 2 + 1)

/-- `ω = h ^ ((q + 1) / 2)`, with `ω ^ q = -ω`. -/
def ω : K := S.h ^ ((S.q + 1) / 2)

theorem q_odd : Odd S.q := S.odd_p.pow

theorem q_pow_mul (n : ℕ) : S.q ^ n = p ^ (S.e * n) := by
  unfold q
  rw [← pow_mul]

theorem card_eq' : Fintype.card K = S.q ^ 4 := S.card_eq

theorem pow_card (x : K) : x ^ (S.q ^ 4) = x := by
  rw [← S.card_eq']
  exact FiniteField.pow_card x

theorem add_pow_q (n : ℕ) (x y : K) : (x + y) ^ S.q ^ n = x ^ S.q ^ n + y ^ S.q ^ n := by
  rw [S.q_pow_mul n]
  exact add_pow_expChar_pow x y p (S.e * n)

theorem pow_q_pow_of_pow_q {c : K} (hc : c ^ S.q = c) (n : ℕ) : c ^ S.q ^ n = c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_mul, ih, hc]

theorem mem_F {x : K} : x ∈ S.F ↔ x ^ S.q = x := Iff.rfl

theorem mem_L {x : K} : x ∈ S.L ↔ x ^ (S.q ^ 2) = x := by
  show x ^ p ^ (2 * S.e) = x ↔ _
  rw [S.q_pow_mul 2, mul_comm]

theorem F_le_L : S.F ≤ S.L := by
  intro x hx
  rw [mem_L]
  rw [mem_F] at hx
  rw [pow_two, pow_mul, hx, hx]

theorem even_q_sq_add_one : Even (S.q ^ 2 + 1) :=
  (S.q_odd.pow).add_one

theorem q_sq_sub_one_mul : S.q ^ 4 - 1 = (S.q ^ 2 - 1) * (S.q ^ 2 + 1) := by
  have h1 : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ (by
    have := S.q_odd.pos
    exact this)
  have : S.q ^ 4 = (S.q ^ 2) ^ 2 := by ring
  rw [this]
  zify [h1, (by nlinarith : 1 ≤ (S.q ^ 2) ^ 2)]
  ring

theorem q_sq_sub_one_mul' : S.q ^ 4 - 1 = (S.q - 1) * ((S.q + 1) * (S.q ^ 2 + 1)) := by
  have hq : 1 ≤ S.q := S.q_odd.pos
  have : S.q ^ 4 - 1 = (S.q - 1) * ((S.q + 1) * (S.q ^ 2 + 1)) := by
    zify [hq, Nat.one_le_pow 4 _ hq]
    ring
  exact this

theorem q_ge_three : 3 ≤ S.q := by
  have h1 : 2 ≠ p := fun h => by
    have := S.odd_p
    rw [← h] at this
    exact absurd this (by decide)
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpodd : 3 ≤ p := by
    rcases S.odd_p with ⟨k, hk⟩
    omega
  have he : S.e ≠ 0 := by
    intro he
    have := S.card_eq
    rw [he, pow_zero] at this
    have := Fintype.one_lt_card (α := K)
    omega
  calc 3 ≤ p := hpodd
    _ = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ S.e := Nat.pow_le_pow_right (by omega) (Nat.one_le_iff_ne_zero.mpr he)

theorem one_lt_q : 1 < S.q := by have := S.q_ge_three; omega

/-- `|F| = q`. -/
theorem natCard_F : Nat.card S.F = S.q := by
  classical
  have hdvd : S.q - 1 ∣ Fintype.card K - 1 := by
    rw [S.card_eq']
    have := Nat.sub_dvd_pow_sub_pow S.q 1 4
    simpa using this
  have key := card_pow_eq_self S.orderOf_g S.one_lt_q hdvd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← key]
  congr 1

/-- `|L| = q²`. -/
theorem natCard_L : Nat.card S.L = S.q ^ 2 := by
  classical
  have hdvd : S.q ^ 2 - 1 ∣ Fintype.card K - 1 := by
    rw [S.card_eq', show S.q ^ 4 = (S.q ^ 2) ^ 2 by ring]
    have := Nat.sub_dvd_pow_sub_pow (S.q ^ 2) 1 2
    rwa [one_pow] at this
  have hm : 1 < S.q ^ 2 := by have := S.one_lt_q; nlinarith
  have key := card_pow_eq_self S.orderOf_g hm hdvd
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← key]
  congr 1
  ext x
  simp [mem_L]

/-- `s = (q² + 1) / 2`, so `q² + 1 = 2 s`. -/
def s : ℕ := (S.q ^ 2 + 1) / 2

theorem q_sq_add_one_eq : S.q ^ 2 + 1 = 2 * S.s := by
  unfold s
  exact (Nat.two_mul_div_two_of_even S.even_q_sq_add_one).symm

theorem N_sub_one : Fintype.card K - 1 = (S.q ^ 2 - 1) * (2 * S.s) := by
  rw [S.card_eq', ← S.q_sq_add_one_eq]
  have h1 : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ S.q_odd.pos
  obtain ⟨t, ht⟩ : ∃ t, S.q ^ 2 = t + 1 := ⟨S.q ^ 2 - 1, by omega⟩
  rw [show S.q ^ 4 = (S.q ^ 2) ^ 2 by ring, ht, show (t + 1) ^ 2 = t * (t + 2) + 1 by ring]
  simp only [Nat.add_sub_cancel]

theorem g_pow_N : S.g ^ (Fintype.card K - 1) = 1 := by
  rw [← S.orderOf_g]
  exact pow_orderOf_eq_one S.g

theorem g_ne_zero : S.g ≠ 0 := by
  intro h0
  have h1 := S.g_pow_N
  rw [h0, zero_pow] at h1
  · exact zero_ne_one h1
  · have := S.one_lt_q
    have := Fintype.one_lt_card (α := K)
    omega

theorem g_pow_half : S.g ^ ((S.q ^ 2 - 1) * S.s) = -1 := by
  have hk : 2 * ((S.q ^ 2 - 1) * S.s) = Fintype.card K - 1 := by
    rw [S.N_sub_one]; ring
  have hpos : 0 < S.q ^ 2 - 1 := by
    have h3 : 3 ≤ S.q := S.q_ge_three
    have : 9 ≤ S.q ^ 2 := by nlinarith
    omega
  have hs : 0 < S.s := by unfold s; have := S.q_odd.pos; omega
  apply pow_eq_neg_one_of_sq
  · rw [hk]; exact S.g_pow_N
  · apply pow_ne_one_of_lt_orderOf
    · exact (Nat.mul_pos hpos hs).ne'
    · rw [S.orderOf_g, S.N_sub_one, show (S.q ^ 2 - 1) * (2 * S.s) = 2 * ((S.q ^ 2 - 1) * S.s) by ring]
      have := Nat.mul_pos hpos hs
      omega


theorem s_pos : 0 < S.s := by
  have h1 : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge_three; omega)
  unfold s
  omega

theorem q_pow_eq (x : K) : x ^ S.q = x ^ (S.q - 1) * x := by
  rw [← pow_succ]
  congr 1
  have := S.q_ge_three
  omega

theorem q_add_sub : (S.q + 1) * (S.q - 1) = S.q ^ 2 - 1 := by
  obtain ⟨t, ht⟩ : ∃ t, S.q = t + 1 := ⟨S.q - 1, by have := S.q_ge_three; omega⟩
  rw [ht, Nat.add_sub_cancel, show (t + 1) ^ 2 = (t + 1 + 1) * t + 1 by ring, Nat.add_sub_cancel]

theorem half_mul : 2 * ((S.q - 1) * ((S.q + 1) / 2)) = S.q ^ 2 - 1 := by
  have he : 2 * ((S.q + 1) / 2) = S.q + 1 := Nat.two_mul_div_two_of_even S.q_odd.add_one
  calc 2 * ((S.q - 1) * ((S.q + 1) / 2)) = (2 * ((S.q + 1) / 2)) * (S.q - 1) := by ring
    _ = S.q ^ 2 - 1 := by rw [he, S.q_add_sub]

theorem d_sq : S.d ^ 2 = S.h := by
  unfold d h
  rw [← pow_mul]
  congr 1
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp S.even_q_sq_add_one)

theorem d_pow_q_sq : S.d ^ (S.q ^ 2) = -S.d := by
  have hk : S.d ^ (S.q ^ 2 - 1) = -1 := by
    unfold d
    rw [← pow_mul]
    have : (S.q ^ 2 + 1) / 2 * (S.q ^ 2 - 1) = (S.q ^ 2 - 1) * S.s := mul_comm _ _
    rw [this, S.g_pow_half]
  have hq : S.q ^ 2 = (S.q ^ 2 - 1) + 1 := by
    have : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge_three; omega)
    omega
  calc S.d ^ (S.q ^ 2) = S.d ^ (S.q ^ 2 - 1) * S.d := by rw [← pow_succ, ← hq]
    _ = -S.d := by rw [hk, neg_one_mul]

theorem orderOf_h : orderOf S.h = S.q ^ 2 - 1 := by
  unfold h
  have hdvd : S.q ^ 2 + 1 ∣ Fintype.card K - 1 := ⟨S.q ^ 2 - 1, by rw [S.N_sub_one, ← S.q_sq_add_one_eq]; ring⟩
  rw [orderOf_pow' _ (by have := S.q_sq_add_one_eq; omega), S.orderOf_g, Nat.gcd_eq_right hdvd,
    S.N_sub_one, ← S.q_sq_add_one_eq, Nat.mul_div_cancel _ (by omega)]

theorem h_pow_q_sq_sub_one : S.h ^ (S.q ^ 2 - 1) = 1 := by
  rw [← S.orderOf_h]
  exact pow_orderOf_eq_one S.h

theorem h_ne_zero : S.h ≠ 0 := by
  unfold h
  exact pow_ne_zero _ S.g_ne_zero

theorem h_pow_half : S.h ^ ((S.q - 1) * ((S.q + 1) / 2)) = -1 := by
  have hk := S.half_mul
  apply pow_eq_neg_one_of_sq
  · rw [hk]; exact S.h_pow_q_sq_sub_one
  · apply pow_ne_one_of_lt_orderOf
    · have h3 : 3 ≤ S.q := S.q_ge_three
      have : 0 < (S.q - 1) * ((S.q + 1) / 2) := Nat.mul_pos (by omega) (by omega)
      exact this.ne'
    · rw [S.orderOf_h]
      have h3 : 3 ≤ S.q := S.q_ge_three
      have : 0 < (S.q - 1) * ((S.q + 1) / 2) := Nat.mul_pos (by omega) (by omega)
      omega

theorem ω_sq : S.ω ^ 2 = S.h ^ (S.q + 1) := by
  unfold ω
  rw [← pow_mul]
  congr 1
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp S.q_odd.add_one)

theorem ω_pow_q : S.ω ^ S.q = -S.ω := by
  have hk : S.ω ^ (S.q - 1) = -1 := by
    unfold ω
    rw [← pow_mul, mul_comm, S.h_pow_half]
  rw [S.q_pow_eq, hk, neg_one_mul]

theorem h_mem_L : S.h ∈ S.L := by
  rw [mem_L]
  have : S.h ^ S.q ^ 2 = S.h := by
    have hq : S.q ^ 2 = (S.q ^ 2 - 1) + 1 := by
      have : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge_three; omega)
      omega
    calc S.h ^ S.q ^ 2 = S.h ^ (S.q ^ 2 - 1) * S.h := by rw [← pow_succ, ← hq]
      _ = S.h := by rw [S.h_pow_q_sq_sub_one, one_mul]
  exact this

theorem ω_mem_L : S.ω ∈ S.L := by
  unfold ω
  exact S.L.pow_mem S.h_mem_L _

theorem N_mem_F : S.h ^ (S.q + 1) ∈ S.F := by
  rw [mem_F, S.q_pow_eq]
  have h1 : (S.h ^ (S.q + 1)) ^ (S.q - 1) = 1 := by
    rw [← pow_mul, S.q_add_sub]
    exact S.h_pow_q_sq_sub_one
  rw [h1, one_mul]

end Setting

end BipartiteDD.SingerC
