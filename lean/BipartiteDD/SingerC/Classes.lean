import BipartiteDD.SingerC.Form

/-! Part (b) of Proposition C: the class of `g ^ i` is `i mod (q + 1)`, and the class is
characterised by the norm `N(z) = z ^ (q² + 1)`: for `z ≠ 0`, `z` lies in class `a` iff
`N(z) ∈ h ^ a · F^×`, where `h = g ^ (q² + 1)`. -/

namespace BipartiteDD.SingerC

open Finset

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- `z` lies in class `a`: `z = g ^ i` for some `i` with `i ≡ a (mod q + 1)`. -/
def InClass (a : ℕ) (z : K) : Prop := ∃ i : ℕ, z = S.g ^ i ∧ i % (S.q + 1) = a

/-- Every nonzero element is a power of the generator `g`. -/
theorem exists_pow_g {z : K} (hz : z ≠ 0) : ∃ j : ℕ, z = S.g ^ j := by
  classical
  have hinj : Set.InjOn (fun n : ℕ => S.g ^ n) (Set.Iio (Fintype.card K - 1)) := by
    rw [← S.orderOf_g]
    exact pow_injOn_Iio_orderOf
  have hsub : (range (Fintype.card K - 1)).image (fun n => S.g ^ n) ⊆
      univ.filter (fun x : K => x ≠ 0) := by
    intro x hx
    obtain ⟨n, -, rfl⟩ := mem_image.mp hx
    simp [pow_ne_zero _ S.g_ne_zero]
  have hcard1 : ((range (Fintype.card K - 1)).image (fun n => S.g ^ n)).card = Fintype.card K - 1 := by
    rw [card_image_of_injOn, card_range]
    intro a ha b hb hab
    exact hinj (by simpa using ha) (by simpa using hb) hab
  have hcard2 : (univ.filter (fun x : K => x ≠ 0)).card = Fintype.card K - 1 := by
    rw [filter_ne' univ (0 : K), card_erase_of_mem (mem_univ _), card_univ]
  have heq := eq_of_subset_of_card_le hsub (by rw [hcard1, hcard2])
  have hz' : z ∈ univ.filter (fun x : K => x ≠ 0) := by simpa using hz
  rw [← heq] at hz'
  obtain ⟨n, -, hn⟩ := mem_image.mp hz'
  exact ⟨n, hn.symm⟩

omit [Fintype K] in
/-- Powers of a nonzero element of a field: `x ^ i = x ^ j` forces `i ≡ j` modulo the order. -/
theorem pow_modEq_of_eq {x : K} (hx : x ≠ 0) {i j : ℕ} (h : x ^ i = x ^ j) :
    i ≡ j [MOD orderOf x] := by
  rcases le_total j i with hji | hij
  · have h1 : x ^ (i - j) = 1 := by
      have h2 : x ^ j * x ^ (i - j) = x ^ j * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hji, h]
      exact mul_left_cancel₀ (pow_ne_zero _ hx) h2
    exact ((Nat.modEq_iff_dvd' hji).mpr (orderOf_dvd_of_pow_eq_one h1)).symm
  · have h1 : x ^ (j - i) = 1 := by
      have h2 : x ^ i * x ^ (j - i) = x ^ i * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hij, h]
      exact mul_left_cancel₀ (pow_ne_zero _ hx) h2
    exact (Nat.modEq_iff_dvd' hij).mpr (orderOf_dvd_of_pow_eq_one h1)

theorem g_pow_eq_iff_modEq {i j : ℕ} (h : S.g ^ i = S.g ^ j) :
    i ≡ j [MOD Fintype.card K - 1] := by
  rw [← S.orderOf_g]
  exact pow_modEq_of_eq S.g_ne_zero h

theorem g_pow_eq_iff_mod {i j : ℕ} (h : S.g ^ i = S.g ^ j) : i % (S.q + 1) = j % (S.q + 1) := by
  have hmod := S.g_pow_eq_iff_modEq h
  have hdvd : S.q + 1 ∣ Fintype.card K - 1 := ⟨(S.q - 1) * (S.q ^ 2 + 1), by
    rw [S.card_eq']
    have := S.q_sq_sub_one_mul'
    rw [this]
    ring⟩
  exact Nat.ModEq.of_dvd hdvd hmod

theorem inClass_unique {a b : ℕ} {z : K} (ha : S.InClass a z) (hb : S.InClass b z) :
    a = b := by
  obtain ⟨i, hi, hia⟩ := ha
  obtain ⟨j, hj, hjb⟩ := hb
  have := S.g_pow_eq_iff_mod (hi.symm.trans hj)
  rw [← hia, ← hjb]
  exact this

/-- Every nonzero element of `F` is a power of `N = h ^ (q + 1)`. -/
theorem exists_N_pow_of_mem_F {c : K} (hcF : c ∈ S.F) (hc0 : c ≠ 0) :
    ∃ t : ℕ, c = (S.h ^ (S.q + 1)) ^ t := by
  obtain ⟨m, hm⟩ := S.exists_pow_g hc0
  have hc1 : c ^ (S.q - 1) = 1 := by
    have h1 : c ^ S.q = c := S.mem_F.mp hcF
    rw [S.q_pow_eq] at h1
    apply mul_right_cancel₀ hc0
    rw [one_mul]
    exact h1
  have hdm : (S.q + 1) * (S.q ^ 2 + 1) ∣ m := by
    have h1 : S.g ^ (m * (S.q - 1)) = 1 := by
      rw [pow_mul, ← hm, hc1]
    have h2 : Fintype.card K - 1 ∣ m * (S.q - 1) := by
      rw [← S.orderOf_g]
      exact orderOf_dvd_of_pow_eq_one h1
    rw [S.card_eq', S.q_sq_sub_one_mul', mul_comm m] at h2
    exact Nat.dvd_of_mul_dvd_mul_left (by have := S.one_lt_q; omega) h2
  obtain ⟨t, ht⟩ := hdm
  refine ⟨t, ?_⟩
  rw [hm, ht]
  unfold h
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

/-- Membership in class `a` in terms of the norm: for `z ≠ 0` and `a ≤ q`,
`z` lies in class `a` iff `z ^ (q² + 1) ∈ h ^ a · F^×`. -/
theorem inClass_iff {a : ℕ} (ha : a < S.q + 1) {z : K} (hz : z ≠ 0) :
    S.InClass a z ↔ ∃ c ∈ S.F, c ≠ 0 ∧ z ^ (S.q ^ 2 + 1) = S.h ^ a * c := by
  constructor
  · rintro ⟨i, rfl, hi⟩
    refine ⟨(S.h ^ (S.q + 1)) ^ (i / (S.q + 1)), S.F.pow_mem S.N_mem_F _,
      pow_ne_zero _ (pow_ne_zero _ S.h_ne_zero), ?_⟩
    have hi' : i = (S.q + 1) * (i / (S.q + 1)) + a := by
      rw [← hi]
      exact (Nat.div_add_mod i (S.q + 1)).symm
    generalize i / (S.q + 1) = k at hi' ⊢
    unfold h
    simp only [← pow_mul, ← pow_add]
    congr 1
    rw [hi']
    ring
  · rintro ⟨c, hcF, hc0, hnorm⟩
    obtain ⟨j, hj⟩ := S.exists_pow_g hz
    obtain ⟨t, hcN⟩ := S.exists_N_pow_of_mem_F hcF hc0
    have hzh : z ^ (S.q ^ 2 + 1) = S.h ^ j := by
      rw [hj]
      unfold h
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    have hj' : S.h ^ j = S.h ^ (a + (S.q + 1) * t) := by
      rw [← hzh, hnorm, hcN, ← pow_mul, ← pow_add]
    have hmod : j ≡ a + (S.q + 1) * t [MOD S.q ^ 2 - 1] := by
      rw [← S.orderOf_h]
      exact pow_modEq_of_eq S.h_ne_zero hj'
    have hmod' : j ≡ a + (S.q + 1) * t [MOD S.q + 1] := by
      apply Nat.ModEq.of_dvd _ hmod
      exact ⟨S.q - 1, by rw [← S.q_add_sub]⟩
    refine ⟨j, hj, ?_⟩
    have h3 : j % (S.q + 1) = (a + (S.q + 1) * t) % (S.q + 1) := hmod'
    rw [h3, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]

end Setting

end BipartiteDD.SingerC
