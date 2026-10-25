import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! # Packed fields ("SWAR") on natural numbers

`pkF w f B = Σ_{j < B} f j * 2^(w j)` packs `B` fields of `w` bits. When every field is below `2 ^ w`, the
kernel's big-number operations act on all fields at once:

* `+`, `* c` and `-` (when no field borrows) act fieldwise (`pkF_add`, `pkF_mul`, `pkF_sub`);
* `&&&` acts fieldwise (`pkF_land`);
* a right shift followed by a mask below `2 ^ (w - s)` acts fieldwise (`pkF_shr_land`);
* packing is injective (`pkF_inj`), and a number below `2 ^ (w B)` is the packing of its own fields (`pkF_fields`).

These are the facts behind the batch checks of `LeanAll.HaarSwar`. -/

namespace BipartiteDD.LeanAll.Swar

/-- `B` fields `f 0, …, f (B-1)` of `w` bits, field `0` lowest. -/
def pkF (w : ℕ) (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | B + 1 => 2 ^ (w * B) * f B + pkF w f B

@[simp] theorem pkF_zero (w : ℕ) (f : ℕ → ℕ) : pkF w f 0 = 0 := rfl

theorem pkF_succ (w : ℕ) (f : ℕ → ℕ) (B : ℕ) : pkF w f (B + 1) = 2 ^ (w * B) * f B + pkF w f B := rfl

theorem pkF_congr {w : ℕ} {f g : ℕ → ℕ} : ∀ {B : ℕ}, (∀ j < B, f j = g j) → pkF w f B = pkF w g B
  | 0, _ => rfl
  | B + 1, h => by
    rw [pkF_succ, pkF_succ, h B (by omega), pkF_congr (fun j hj => h j (by omega))]

theorem pkF_lt {w : ℕ} {f : ℕ → ℕ} : ∀ {B : ℕ}, (∀ j < B, f j < 2 ^ w) → pkF w f B < 2 ^ (w * B)
  | 0, _ => by simp
  | B + 1, h => by
    rw [pkF_succ]
    have h1 := pkF_lt (B := B) (fun j hj => h j (by omega))
    have h2 := h B (by omega)
    have e : 2 ^ (w * (B + 1)) = 2 ^ (w * B) * 2 ^ w := by rw [Nat.mul_succ, pow_add]
    rw [e]
    calc 2 ^ (w * B) * f B + pkF w f B < 2 ^ (w * B) * f B + 2 ^ (w * B) := by omega
      _ = 2 ^ (w * B) * (f B + 1) := by ring
      _ ≤ 2 ^ (w * B) * 2 ^ w := Nat.mul_le_mul_left _ h2

/-! ## Arithmetic, fieldwise -/

theorem pkF_add (w : ℕ) (f g : ℕ → ℕ) : ∀ B, pkF w (fun j => f j + g j) B = pkF w f B + pkF w g B
  | 0 => rfl
  | B + 1 => by rw [pkF_succ, pkF_succ, pkF_succ, pkF_add w f g B]; ring

theorem pkF_mul (w c : ℕ) (f : ℕ → ℕ) : ∀ B, pkF w (fun j => c * f j) B = c * pkF w f B
  | 0 => by simp
  | B + 1 => by rw [pkF_succ, pkF_succ, pkF_mul w c f B]; ring

theorem pkF_sub {w : ℕ} {f g : ℕ → ℕ} {B : ℕ} (h : ∀ j < B, g j ≤ f j) :
    pkF w (fun j => f j - g j) B = pkF w f B - pkF w g B := by
  have e : pkF w (fun j => (f j - g j) + g j) B = pkF w f B :=
    pkF_congr (fun j hj => Nat.sub_add_cancel (h j hj))
  rw [pkF_add] at e
  omega

theorem pkF_const (w c : ℕ) (B : ℕ) : pkF w (fun _ => c) B = c * pkF w (fun _ => 1) B := by
  rw [← pkF_mul]; simp

/-- The all-ones packing in closed form. -/
theorem pkF_one_mul (w : ℕ) : ∀ B, pkF w (fun _ => 1) B * (2 ^ w - 1) = 2 ^ (w * B) - 1
  | 0 => by simp
  | B + 1 => by
    rw [pkF_succ, add_mul, pkF_one_mul w B]
    have h1 : 1 ≤ 2 ^ w := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ (w * B) := Nat.one_le_two_pow
    have e : 2 ^ (w * (B + 1)) = 2 ^ (w * B) * 2 ^ w := by rw [Nat.mul_succ, pow_add]
    rw [e, mul_one]
    zify [h1, h2, Nat.one_le_two_pow (n := w * B + w), Nat.mul_le_mul h2 h1]
    push_cast
    ring

theorem pkF_one_eq (w B : ℕ) (hw : 1 ≤ w) : pkF w (fun _ => 1) B = (2 ^ (w * B) - 1) / (2 ^ w - 1) := by
  have h : 0 < 2 ^ w - 1 := by
    have : 2 ≤ 2 ^ w := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
    omega
  rw [← pkF_one_mul w B, Nat.mul_div_cancel _ h]

/-! ## Bits -/

theorem testBit_pkF {w : ℕ} (hw : 0 < w) {f : ℕ → ℕ} : ∀ {B : ℕ}, (∀ j < B, f j < 2 ^ w) → ∀ i,
    (pkF w f B).testBit i = (decide (i < w * B) && (f (i / w)).testBit (i % w))
  | 0, _, i => by simp
  | B + 1, h, i => by
    rw [pkF_succ, Nat.testBit_two_pow_mul_add _ (pkF_lt (fun j hj => h j (by omega)))]
    by_cases hi : i < w * B
    · rw [if_pos hi, testBit_pkF hw (fun j hj => h j (by omega)) i]
      simp [hi, show i < w * (B + 1) by nlinarith]
    · rw [if_neg hi]
      have hq : w * B ≤ i := by omega
      by_cases hi2 : i < w * (B + 1)
      · have e1 : i / w = B :=
          Nat.div_eq_of_lt_le (by rw [Nat.mul_comm]; exact hq) (by rw [Nat.mul_comm]; exact hi2)
        have e2 : i % w = i - w * B := by
          have := Nat.mod_add_div i w
          rw [e1] at this
          omega
        simp [hi2, e1, e2]
      · have hb : (f B).testBit (i - w * B) = false := by
          apply Nat.testBit_lt_two_pow
          calc f B < 2 ^ w := h B (by omega)
            _ ≤ 2 ^ (i - w * B) := Nat.pow_le_pow_right (by norm_num) (by rw [Nat.mul_succ] at hi2; omega)
        simp [hi2, hb]

/-- A number below `2 ^ (w B)` is the packing of its own fields. -/
theorem pkF_fields {w : ℕ} (hw : 0 < w) (x : ℕ) : ∀ {B : ℕ}, x < 2 ^ (w * B) →
    pkF w (fun j => x / 2 ^ (w * j) % 2 ^ w) B = x := by
  intro B hx
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pkF hw (fun j _ => Nat.mod_lt _ (by positivity))]
  rw [Nat.testBit_mod_two_pow]
  have hdiv : (x / 2 ^ (w * (i / w))).testBit (i % w) = x.testBit i := by
    rw [← Nat.testBit_add, Nat.add_comm, Nat.div_add_mod]
  by_cases hi : i < w * B
  · simp [hi, Nat.mod_lt i hw, hdiv]
  · have : x.testBit i = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))
    simp [hi, this]

/-- Packing is injective on fields below `2 ^ w`. -/
theorem pkF_inj {w : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} {B : ℕ} (hf : ∀ j < B, f j < 2 ^ w)
    (hg : ∀ j < B, g j < 2 ^ w) (h : pkF w f B = pkF w g B) : ∀ j < B, f j = g j := by
  intro j hj
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < w
  · have e1 := testBit_pkF hw hf (w * j + k)
    have e2 := testBit_pkF hw hg (w * j + k)
    rw [h] at e1
    have hd : (w * j + k) / w = j := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hk, Nat.zero_add]
    have hm : (w * j + k) % w = k := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
    have hlt : w * j + k < w * B := by nlinarith
    simp only [hd, hm, hlt, decide_true, Bool.true_and] at e1 e2
    rw [← e1, e2]
  · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le (hf j hj) (Nat.pow_le_pow_right (by norm_num) (by omega))),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le (hg j hj) (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-- `&&&` is fieldwise. -/
theorem pkF_land {w : ℕ} (hw : 0 < w) {f g : ℕ → ℕ} {B : ℕ} (hf : ∀ j < B, f j < 2 ^ w)
    (hg : ∀ j < B, g j < 2 ^ w) : pkF w f B &&& pkF w g B = pkF w (fun j => f j &&& g j) B := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hfg : ∀ j < B, f j &&& g j < 2 ^ w := fun j hj => Nat.and_lt_two_pow _ (hg j hj)
  rw [Nat.testBit_and, testBit_pkF hw hf, testBit_pkF hw hg, testBit_pkF hw hfg, Nat.testBit_and]
  cases decide (i < w * B) <;> simp

/-- A right shift by `s ≤ w` followed by a mask below `2 ^ (w - s)` is fieldwise. -/
theorem pkF_shr_land {w s c : ℕ} (hw : 0 < w) (hs : s ≤ w) (hc : c < 2 ^ (w - s)) {f : ℕ → ℕ} {B : ℕ}
    (hf : ∀ j < B, f j < 2 ^ w) :
    (pkF w f B >>> s) &&& pkF w (fun _ => c) B = pkF w (fun j => (f j >>> s) &&& c) B := by
  have hc' : c < 2 ^ w := lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hr : ∀ j < B, (f j >>> s) &&& c < 2 ^ w := fun j _ => Nat.and_lt_two_pow _ hc'
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_pkF hw hf, testBit_pkF hw (fun _ _ => hc'),
    testBit_pkF hw hr, Nat.testBit_and, Nat.testBit_shiftRight]
  by_cases hi : i < w * B
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hcb : c.testBit (i % w)
    · -- the mask bit is set, so `i % w < w - s` and the shifted bit stays in the field
      have hlt : i % w < w - s := by
        by_contra hge
        push_neg at hge
        have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) hge))
        rw [this] at hcb
        exact absurd hcb (by simp)
      have h4 := Nat.mod_add_div i w
      have h2 : i / w < B := by
        rw [Nat.div_lt_iff_lt_mul hw]; linarith
      have h5 : s + i % w < w := by omega
      have hsi : s + i < w * B :=
        calc s + i = (s + i % w) + w * (i / w) := by omega
          _ < w + w * (i / w) := by omega
          _ = w * (i / w + 1) := by ring
          _ ≤ w * B := Nat.mul_le_mul_left _ (by omega)
      have hd : (s + i) / w = i / w := by
        apply Nat.div_eq_of_lt_le
        · have : i / w * w ≤ i := Nat.div_mul_le_self i w
          omega
        · calc s + i = (s + i % w) + w * (i / w) := by omega
            _ < w + w * (i / w) := by omega
            _ = (i / w + 1) * w := by ring
      have hm : (s + i) % w = s + i % w := by
        have h3 := Nat.mod_add_div (s + i) w
        have h4 := Nat.mod_add_div i w
        rw [hd] at h3
        omega
      simp [hsi, hd, hm, hcb]
    · simp [hcb]
  · simp [hi]

end BipartiteDD.LeanAll.Swar
