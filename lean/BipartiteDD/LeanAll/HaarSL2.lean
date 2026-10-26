import BipartiteDD.LeanAll.HaarSwar2
import BipartiteDD.Haar.GraphD
import BipartiteDD.Haar.Main
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum.Prime

/-! # (Copy of `HaarSL.lean` over `Core/HaarCore.lean`.) Haar graphs of `SL(2, p) × Z_n` from batch certificates

The group is `G p n = SL(2, ZMod p) × Multiplicative (ZMod n)`. Its elements are numbered by `idx`: the matrix
`(a b; c d)` gets `i = (a (p-1) + (c-1)) p + d` when `c ≠ 0` and `i = p² (p-1) + (a-1) p + b` when `c = 0`, and
`(A, z)` gets `i n + z`. So `|G| = p (p² - 1) n` (`card_G`), and batch `b` of `p n` slots holds the indices
`[b p n, (b+1) p n)`: for `b < p (p-1)` the matrices with `a = b / (p-1)`, `c = b % (p-1) + 1` and slot `d n + z`;
for the others `c = 0`, `a = b - p (p-1) + 1` and slot `b' n + z` (`b'` the upper right entry).

`cover_of_batches` turns passing batch checks for all `p² - 1` batches into: every element is the product of the
`L` letters of some word. -/

namespace BipartiteDD.LeanAll.HaarSL2

open BipartiteDD.LeanAll.HaarSwar2 BipartiteDD.LeanAll.Swar Matrix

variable {p n : ℕ}

/-- The group. -/
abbrev G (p n : ℕ) := SpecialLinearGroup (Fin 2) (ZMod p) × Multiplicative (ZMod n)

theorem det_entries (A : SpecialLinearGroup (Fin 2) (ZMod p)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rw [det_fin_two] at h
  exact h

theorem p_two [hp : Fact p.Prime] : 2 ≤ p := hp.out.two_le

/-! ## Numbering -/

/-- The number of a matrix. -/
def slotSL (A : SpecialLinearGroup (Fin 2) (ZMod p)) : ℕ :=
  if A 1 0 ≠ 0 then ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + (A 1 1).val
  else p * p * (p - 1) + ((A 0 0).val - 1) * p + (A 0 1).val

theorem val_pos_of_ne {x : ZMod p} (hx : x ≠ 0) : 1 ≤ x.val := by
  rcases Nat.eq_zero_or_pos x.val with h | h
  · exact absurd ((ZMod.val_eq_zero x).1 h) hx
  · exact h

theorem slotSL_lt [Fact p.Prime] (A : SpecialLinearGroup (Fin 2) (ZMod p)) : slotSL A < p * (p * p - 1) := by
  have h2 := p_two (p := p)
  have ha := ZMod.val_lt (A 0 0)
  have hb := ZMod.val_lt (A 0 1)
  have hc := ZMod.val_lt (A 1 0)
  have hd := ZMod.val_lt (A 1 1)
  have e : p * (p * p - 1) = p * p * (p - 1) + (p - 1) * p := by
    zify [show 1 ≤ p by omega, show 1 ≤ p * p by nlinarith]; ring
  unfold slotSL
  split_ifs with h
  · have hc1 := val_pos_of_ne h
    have : (A 0 0).val * (p - 1) + ((A 1 0).val - 1) < p * (p - 1) := by
      calc (A 0 0).val * (p - 1) + ((A 1 0).val - 1) < (A 0 0).val * (p - 1) + (p - 1) := by omega
        _ = ((A 0 0).val + 1) * (p - 1) := by ring
        _ ≤ p * (p - 1) := Nat.mul_le_mul_right _ ha
    rw [e]
    calc ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + (A 1 1).val
        < ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + p := by omega
      _ = ((A 0 0).val * (p - 1) + ((A 1 0).val - 1) + 1) * p := by ring
      _ ≤ (p * (p - 1)) * p := Nat.mul_le_mul_right _ this
      _ = p * p * (p - 1) := by ring
      _ ≤ p * p * (p - 1) + (p - 1) * p := Nat.le_add_right _ _
  · push_neg at h
    have hdet := det_entries A
    rw [h, mul_zero, sub_zero] at hdet
    have ha0 : A 0 0 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
    have ha1 := val_pos_of_ne ha0
    rw [e]
    have : ((A 0 0).val - 1) * p + (A 0 1).val < (p - 1) * p := by
      calc ((A 0 0).val - 1) * p + (A 0 1).val < ((A 0 0).val - 1) * p + p := by omega
        _ = ((A 0 0).val - 1 + 1) * p := by ring
        _ ≤ (p - 1) * p := Nat.mul_le_mul_right _ (by omega)
    omega

theorem cast_val_lt {k : ℕ} (hk : k < p) : ((k : ℕ) : ZMod p).val = k := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hk]

theorem slotSL_c [Fact p.Prime] (A : SpecialLinearGroup (Fin 2) (ZMod p)) (h : A 1 0 ≠ 0) :
    slotSL A < p * p * (p - 1) ∧ slotSL A % p = (A 1 1).val ∧
    slotSL A / p % (p - 1) + 1 = (A 1 0).val ∧ slotSL A / p / (p - 1) = (A 0 0).val := by
  have h2 := p_two (p := p)
  have ha := ZMod.val_lt (A 0 0)
  have hc := ZMod.val_lt (A 1 0)
  have hd := ZMod.val_lt (A 1 1)
  have hc1 := val_pos_of_ne h
  have hs : slotSL A = ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + (A 1 1).val := by
    unfold slotSL; rw [if_pos h]
  have hq : slotSL A / p = (A 0 0).val * (p - 1) + ((A 1 0).val - 1) := by
    rw [hs, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : (A 0 0).val * (p - 1) + ((A 1 0).val - 1) < p * (p - 1) := by
      calc (A 0 0).val * (p - 1) + ((A 1 0).val - 1) < (A 0 0).val * (p - 1) + (p - 1) := by omega
        _ = ((A 0 0).val + 1) * (p - 1) := by ring
        _ ≤ p * (p - 1) := Nat.mul_le_mul_right _ ha
    rw [hs]
    calc ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + (A 1 1).val
        < ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) * p + p := by omega
      _ = ((A 0 0).val * (p - 1) + ((A 1 0).val - 1) + 1) * p := by ring
      _ ≤ (p * (p - 1)) * p := Nat.mul_le_mul_right _ this
      _ = p * p * (p - 1) := by ring
  · rw [hs, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  · rw [hq, Nat.add_comm (_ * (p - 1)), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]; omega
  · rw [hq, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem a_ne_of_c [Fact p.Prime] (A : SpecialLinearGroup (Fin 2) (ZMod p)) (h : A 1 0 = 0) : A 0 0 ≠ 0 := by
  have hdet := det_entries A
  rw [h, mul_zero, sub_zero] at hdet
  intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet

theorem slotSL_nc [Fact p.Prime] (A : SpecialLinearGroup (Fin 2) (ZMod p)) (h : A 1 0 = 0) :
    p * p * (p - 1) ≤ slotSL A ∧ (slotSL A - p * p * (p - 1)) % p = (A 0 1).val ∧
    (slotSL A - p * p * (p - 1)) / p + 1 = (A 0 0).val := by
  have h2 := p_two (p := p)
  have hb := ZMod.val_lt (A 0 1)
  have ha1 := val_pos_of_ne (a_ne_of_c A h)
  have hs : slotSL A = p * p * (p - 1) + ((A 0 0).val - 1) * p + (A 0 1).val := by
    unfold slotSL; rw [if_neg (not_not.mpr h)]
  have e : slotSL A - p * p * (p - 1) = ((A 0 0).val - 1) * p + (A 0 1).val := by omega
  refine ⟨by omega, ?_, ?_⟩
  · rw [e, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  · rw [e, Nat.add_comm (_ * p), Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb]; omega

theorem entry_eq_of_val [Fact p.Prime] {x y : ZMod p} (h : x.val = y.val) : x = y := ZMod.val_injective p h

theorem slotSL_inj [Fact p.Prime] {A B : SpecialLinearGroup (Fin 2) (ZMod p)} (h : slotSL A = slotSL B) : A = B := by
  have hA := det_entries A
  have hB := det_entries B
  by_cases hcA : A 1 0 = 0 <;> by_cases hcB : B 1 0 = 0
  · obtain ⟨-, hA1, hA2⟩ := slotSL_nc A hcA
    obtain ⟨-, hB1, hB2⟩ := slotSL_nc B hcB
    rw [h] at hA1 hA2
    have e00 : A 0 0 = B 0 0 := entry_eq_of_val (by omega)
    have e01 : A 0 1 = B 0 1 := entry_eq_of_val (by omega)
    rw [hcA, mul_zero, sub_zero] at hA
    rw [hcB, mul_zero, sub_zero] at hB
    have e11 : A 1 1 = B 1 1 := by
      have ha := a_ne_of_c A hcA
      have : A 0 0 * (A 1 1 - B 1 1) = 0 := by rw [mul_sub, hA, e00, hB, sub_self]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 ha
      · exact sub_eq_zero.mp h0
    apply SpecialLinearGroup.ext
    intro i j; fin_cases i <;> fin_cases j
    exacts [e00, e01, hcA.trans hcB.symm, e11]
  · exact absurd ((slotSL_c B hcB).1) (by have := (slotSL_nc A hcA).1; omega)
  · exact absurd ((slotSL_c A hcA).1) (by have := (slotSL_nc B hcB).1; omega)
  · obtain ⟨-, hA1, hA2, hA3⟩ := slotSL_c A hcA
    obtain ⟨-, hB1, hB2, hB3⟩ := slotSL_c B hcB
    rw [h] at hA1 hA2 hA3
    have e00 : A 0 0 = B 0 0 := entry_eq_of_val (by omega)
    have e10 : A 1 0 = B 1 0 := entry_eq_of_val (by omega)
    have e11 : A 1 1 = B 1 1 := entry_eq_of_val (by omega)
    have e01 : A 0 1 = B 0 1 := by
      have : (A 0 1 - B 0 1) * A 1 0 = 0 := by
        rw [sub_mul]
        have h1 : A 0 1 * A 1 0 = A 0 0 * A 1 1 - 1 := by linear_combination -hA
        have h2 : B 0 1 * A 1 0 = A 0 0 * A 1 1 - 1 := by rw [e10, e00, e11]; linear_combination -hB
        rw [h1, h2, sub_self]
      rcases mul_eq_zero.mp this with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hcA
    apply SpecialLinearGroup.ext
    intro i j; fin_cases i <;> fin_cases j
    exacts [e00, e01, e10, e11]

theorem cast_ne_zero_of [Fact p.Prime] {k : ℕ} (h1 : 1 ≤ k) (h2 : k < p) : ((k : ℕ) : ZMod p) ≠ 0 := by
  intro h
  have := cast_val_lt (p := p) h2
  rw [h, ZMod.val_zero] at this
  omega

/-- The matrix with entries `a, (a d - 1) / c; c, d`. -/
def mkC [Fact p.Prime] (a c d : ℕ) (hc : ((c : ℕ) : ZMod p) ≠ 0) : SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![(a : ZMod p), ((a : ZMod p) * d - 1) * (c : ZMod p)⁻¹; (c : ZMod p), (d : ZMod p)], by
    rw [det_fin_two_of]; field_simp; ring⟩

/-- The matrix with entries `a, b; 0, 1 / a`. -/
def mkN [Fact p.Prime] (a b : ℕ) (ha : ((a : ℕ) : ZMod p) ≠ 0) : SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨!![(a : ZMod p), (b : ZMod p); 0, (a : ZMod p)⁻¹], by
    rw [det_fin_two_of]; field_simp; ring⟩

theorem slotSL_surj [Fact p.Prime] (i : ℕ) (hi : i < p * (p * p - 1)) : ∃ A : SpecialLinearGroup (Fin 2) (ZMod p), slotSL A = i := by
  have h2 := p_two (p := p)
  have e : p * (p * p - 1) = p * p * (p - 1) + (p - 1) * p := by
    zify [show 1 ≤ p by omega, show 1 ≤ p * p by nlinarith]; ring
  by_cases hlt : i < p * p * (p - 1)
  · have hq : i / p < p * (p - 1) := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
    have ha : i / p / (p - 1) < p := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
    have hc1 : 1 ≤ i / p % (p - 1) + 1 := by omega
    have hc2 : i / p % (p - 1) + 1 < p := by
      have := Nat.mod_lt (i / p) (show 0 < p - 1 by omega); omega
    have hd : i % p < p := Nat.mod_lt _ (by omega)
    have hc := cast_ne_zero_of (p := p) hc1 hc2
    refine ⟨mkC (i / p / (p - 1)) (i / p % (p - 1) + 1) (i % p) hc, ?_⟩
    unfold slotSL
    have e10 : (mkC (p := p) (i / p / (p - 1)) (i / p % (p - 1) + 1) (i % p) hc) 1 0 =
        ((i / p % (p - 1) + 1 : ℕ) : ZMod p) := by simp [mkC]
    have e00 : (mkC (p := p) (i / p / (p - 1)) (i / p % (p - 1) + 1) (i % p) hc) 0 0 =
        ((i / p / (p - 1) : ℕ) : ZMod p) := by simp [mkC]
    have e11 : (mkC (p := p) (i / p / (p - 1)) (i / p % (p - 1) + 1) (i % p) hc) 1 1 =
        ((i % p : ℕ) : ZMod p) := by simp [mkC]
    rw [if_pos (by rw [e10]; exact hc), e00, e10, e11, cast_val_lt ha, cast_val_lt hc2, cast_val_lt hd]
    have h3 := Nat.div_add_mod (i / p) (p - 1)
    have h4 := Nat.div_add_mod i p
    rw [show i / p % (p - 1) + 1 - 1 = i / p % (p - 1) by omega]
    calc (i / p / (p - 1) * (p - 1) + i / p % (p - 1)) * p + i % p
        = ((p - 1) * (i / p / (p - 1)) + i / p % (p - 1)) * p + i % p := by ring
      _ = i := by rw [h3, mul_comm]; exact h4
  · have hr : i - p * p * (p - 1) < (p - 1) * p := by omega
    have ha1 : 1 ≤ (i - p * p * (p - 1)) / p + 1 := Nat.le_add_left _ _
    have ha2 : (i - p * p * (p - 1)) / p + 1 < p := by
      have : (i - p * p * (p - 1)) / p < p - 1 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; exact hr
      omega
    have hb : (i - p * p * (p - 1)) % p < p := Nat.mod_lt _ (by omega)
    have ha := cast_ne_zero_of (p := p) ha1 ha2
    refine ⟨mkN ((i - p * p * (p - 1)) / p + 1) ((i - p * p * (p - 1)) % p) ha, ?_⟩
    unfold slotSL
    have e10 : (mkN (p := p) ((i - p * p * (p - 1)) / p + 1) ((i - p * p * (p - 1)) % p) ha) 1 0 = 0 := by
      simp [mkN]
    have e00 : (mkN (p := p) ((i - p * p * (p - 1)) / p + 1) ((i - p * p * (p - 1)) % p) ha) 0 0 =
        (((i - p * p * (p - 1)) / p + 1 : ℕ) : ZMod p) := by simp [mkN]
    have e01 : (mkN (p := p) ((i - p * p * (p - 1)) / p + 1) ((i - p * p * (p - 1)) % p) ha) 0 1 =
        (((i - p * p * (p - 1)) % p : ℕ) : ZMod p) := by simp [mkN]
    rw [if_neg (by rw [e10]; simp), e00, e01, cast_val_lt ha2, cast_val_lt hb]
    have h4 := Nat.div_add_mod (i - p * p * (p - 1)) p
    rw [show (i - p * p * (p - 1)) / p + 1 - 1 = (i - p * p * (p - 1)) / p by omega]
    calc p * p * (p - 1) + (i - p * p * (p - 1)) / p * p + (i - p * p * (p - 1)) % p
        = p * p * (p - 1) + (p * ((i - p * p * (p - 1)) / p) + (i - p * p * (p - 1)) % p) := by ring
      _ = i := by rw [h4]; omega

/-- `|SL(2, p)| = p (p² - 1)`. -/
theorem card_SL [Fact p.Prime] : Fintype.card (SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p * p - 1) := by
  let f : SpecialLinearGroup (Fin 2) (ZMod p) → Fin (p * (p * p - 1)) := fun A => ⟨slotSL A, slotSL_lt A⟩
  have hf : Function.Bijective f := by
    refine ⟨fun A B h => slotSL_inj (congrArg Fin.val h), fun i => ?_⟩
    obtain ⟨A, hA⟩ := slotSL_surj i.val i.isLt
    exact ⟨A, Fin.ext hA⟩
  rw [Fintype.card_congr (Equiv.ofBijective f hf), Fintype.card_fin]

/-! ## Generators and words -/

theorem card_G [NeZero n] [Fact p.Prime] : Fintype.card (G p n) = p * (p * p - 1) * n := by
  rw [Fintype.card_prod, card_SL, Fintype.card_multiplicative, ZMod.card]

/-- The matrix `(a b; c d)` if its determinant is `1` (else the identity). -/
def mkSL (a b c d : ℕ) : SpecialLinearGroup (Fin 2) (ZMod p) :=
  if h : (a : ZMod p) * d - b * c = 1 then ⟨!![(a : ZMod p), b; c, d], by rw [det_fin_two_of]; exact h⟩ else 1

/-- The group element of a letter. -/
def gOf (l : Let) : G p n := (mkSL l.e l.f l.g l.h, Multiplicative.ofAdd (l.zw : ZMod n))

/-- The determinant condition of a letter. -/
def DetOK (p : ℕ) (l : Let) : Prop := (l.e : ZMod p) * l.h - l.f * l.g = 1

instance (l : Let) : Decidable (DetOK p l) := by unfold DetOK; infer_instance

theorem gOf_entries {l : Let} (h : DetOK p l) :
    (gOf (n := n) l).1 0 0 = (l.e : ZMod p) ∧ (gOf (n := n) l).1 0 1 = (l.f : ZMod p) ∧
      (gOf (n := n) l).1 1 0 = (l.g : ZMod p) ∧ (gOf (n := n) l).1 1 1 = (l.h : ZMod p) ∧
      Multiplicative.toAdd (gOf (p := p) (n := n) l).2 = (l.zw : ZMod n) := by
  unfold DetOK at h
  unfold gOf mkSL
  simp [h]

theorem inv_entries (A : SpecialLinearGroup (Fin 2) (ZMod p)) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]

theorem cast_sub_of_le {q k : ℕ} (hk : k ≤ q) : (((q - k : ℕ)) : ZMod q) = -(k : ZMod q) := by
  rw [Nat.cast_sub hk, ZMod.natCast_self, zero_sub]

variable (sG : ℕ → G p n) (invAt : ℕ → Bool)

/-- Letter `u` at step `t`: the generator or its inverse. -/
def letterG (t u : ℕ) : G p n := cond (invAt t) (sG u)⁻¹ (sG u)

/-- The product of the first `t` letters of the word with digits `dg`. -/
def wordG (dg : ℕ → ℕ) : ℕ → G p n
  | 0 => 1
  | t + 1 => wordG dg t * letterG sG invAt t (dg t)

theorem wordG_succ (dg : ℕ → ℕ) (t : ℕ) :
    wordG sG invAt dg (t + 1) = wordG sG invAt dg t * letterG sG invAt t (dg t) := rfl

/-- The letter table `lt` describes the letters (entries mod `p`, shifts mod `n`). -/
def LetRep (Δ L : ℕ) (lt : ℕ → ℕ → Let) : Prop :=
  ∀ t < L, ∀ u < Δ, ((lt t u).e : ZMod p) = (letterG sG invAt t u).1 0 0 ∧
    ((lt t u).f : ZMod p) = (letterG sG invAt t u).1 0 1 ∧
    ((lt t u).g : ZMod p) = (letterG sG invAt t u).1 1 0 ∧
    ((lt t u).h : ZMod p) = (letterG sG invAt t u).1 1 1 ∧
    ((lt t u).zw : ZMod n) = Multiplicative.toAdd (letterG sG invAt t u).2

/-- With `sG = gOf ∘ genL` and `lt t u` the generator or its `invLet`, the table describes the letters. -/
theorem letRep_of (Δ L : ℕ) (genL : ℕ → Let) (hsG : ∀ u < Δ, sG u = gOf (genL u))
    (hdet : ∀ u < Δ, DetOK p (genL u)) (hb : ∀ u < Δ, (genL u).f ≤ p ∧ (genL u).g ≤ p ∧ (genL u).zw ≤ n)
    (lt : ℕ → ℕ → Let) (hlt : ∀ t u, lt t u = cond (invAt t) (invLet p n (genL u)) (genL u)) :
    LetRep sG invAt Δ L lt := by
  intro t _ u hu
  obtain ⟨h00, h01, h10, h11, hz⟩ := gOf_entries (p := p) (n := n) (hdet u hu)
  rw [hlt, letterG, hsG u hu]
  cases invAt t
  · simp only [cond_false]
    exact ⟨h00.symm, h01.symm, h10.symm, h11.symm, hz.symm⟩
  · simp only [cond_true, invLet]
    obtain ⟨i00, i01, i10, i11⟩ := inv_entries (p := p) (gOf (p := p) (n := n) (genL u)).1
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [Prod.fst_inv, i00, h11]
    · rw [Prod.fst_inv, i01, h01, ZMod.natCast_mod, cast_sub_of_le (hb u hu).1]
    · rw [Prod.fst_inv, i10, h10, ZMod.natCast_mod, cast_sub_of_le (hb u hu).2.1]
    · rw [Prod.fst_inv, i11, h00]
    · rw [Prod.snd_inv, toAdd_inv, hz, ZMod.natCast_mod, cast_sub_of_le (hb u hu).2.2]

theorem semN_rep {Δ L : ℕ} {lt : ℕ → ℕ → Let} (hrep : LetRep sG invAt Δ L lt) (dg : ℕ → ℕ) :
    ∀ t ≤ L, (∀ t' < t, dg t' < Δ) →
      ((semN lt dg t).a : ZMod p) = (wordG sG invAt dg t).1 0 0 ∧
      ((semN lt dg t).b : ZMod p) = (wordG sG invAt dg t).1 0 1 ∧
      ((semN lt dg t).c : ZMod p) = (wordG sG invAt dg t).1 1 0 ∧
      ((semN lt dg t).d : ZMod p) = (wordG sG invAt dg t).1 1 1 ∧
      ((semN lt dg t).z : ZMod n) = Multiplicative.toAdd (wordG sG invAt dg t).2 := by
  intro t
  induction t with
  | zero =>
    intro _ _
    simp [semN, wordG]
  | succ t ih =>
    intro ht hdg
    obtain ⟨ia, ib, ic, id, iz⟩ := ih (by omega) (fun t' h => hdg t' (by omega))
    obtain ⟨le, lf, lg, lh, lz⟩ := hrep t (by omega) (dg t) (hdg t (by omega))
    have hm : (wordG sG invAt dg (t + 1)).1 =
        (wordG sG invAt dg t).1 * (letterG sG invAt t (dg t)).1 := rfl
    have hz : (wordG sG invAt dg (t + 1)).2 = (wordG sG invAt dg t).2 * (letterG sG invAt t (dg t)).2 := rfl
    have e : ∀ i j, (wordG sG invAt dg (t + 1)).1 i j =
        (wordG sG invAt dg t).1 i 0 * (letterG sG invAt t (dg t)).1 0 j +
        (wordG sG invAt dg t).1 i 1 * (letterG sG invAt t (dg t)).1 1 j := by
      intro i j
      rw [hm, SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [semN, mulSt, Nat.cast_add, Nat.cast_mul]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [e, ia, ib, le, lg]
    · rw [e, ia, ib, lf, lh]
    · rw [e, ic, id, le, lg]
    · rw [e, ic, id, lf, lh]
    · rw [hz, toAdd_mul, iz, lz]

/-! ## Batches and the cover -/

/-- All `p² - 1` batches pass, each with some certificate. -/
def BatchesOK (P : Prm) (ONES RD RZ : ℕ) (lt : ℕ → ℕ → Let) : Prop :=
  ∀ b < P.p * P.p - 1, ∃ Dig, batchOK P ONES lt Dig (kindB P.p b) (aB P.p b * ONES) (cond (kindB P.p b) RD 0)
    (cB P.p b * ONES) (cond (kindB P.p b) 0 RD) RZ = true

theorem cast_of_modEq {q x y : ℕ} (h : x ≡ y [MOD q]) : (x : ZMod q) = y :=
  (ZMod.natCast_eq_natCast_iff _ _ _).2 h

theorem bat_nc {p a : ℕ} (h2 : 2 ≤ p) (ha1 : 1 ≤ a) (ha : a < p) :
    kindB p (p * (p - 1) + (a - 1)) = true ∧ aB p (p * (p - 1) + (a - 1)) = a ∧
      cB p (p * (p - 1) + (a - 1)) = 0 ∧ p * (p - 1) + (a - 1) < p * p - 1 := by
  have e : p * p - 1 = p * (p - 1) + (p - 1) := by
    zify [show 1 ≤ p by omega, show 1 ≤ p * p by nlinarith]; ring
  have hk : kindB p (p * (p - 1) + (a - 1)) = true := by
    unfold kindB; rw [Nat.ble_eq]; omega
  refine ⟨hk, ?_, ?_, by omega⟩
  · unfold aB; rw [hk, cond_true]; omega
  · unfold cB; rw [hk, cond_true]

theorem bat_c {p a c : ℕ} (h2 : 2 ≤ p) (ha : a < p) (hc1 : 1 ≤ c) (hc : c < p) :
    kindB p (a * (p - 1) + (c - 1)) = false ∧ aB p (a * (p - 1) + (c - 1)) = a ∧
      cB p (a * (p - 1) + (c - 1)) = c ∧ a * (p - 1) + (c - 1) < p * p - 1 := by
  have e : p * p - 1 = p * (p - 1) + (p - 1) := by
    zify [show 1 ≤ p by omega, show 1 ≤ p * p by nlinarith]; ring
  have hlt : a * (p - 1) + (c - 1) < p * (p - 1) := by
    calc a * (p - 1) + (c - 1) < a * (p - 1) + (p - 1) := by omega
      _ = (a + 1) * (p - 1) := by ring
      _ ≤ p * (p - 1) := Nat.mul_le_mul_right _ ha
  have hk : kindB p (a * (p - 1) + (c - 1)) = false := by
    have : ¬ p * (p - 1) ≤ a * (p - 1) + (c - 1) := by omega
    unfold kindB
    exact Bool.eq_false_iff.mpr (fun h => this (Nat.le_of_ble_eq_true h))
  refine ⟨hk, ?_, ?_, by omega⟩
  · unfold aB; rw [hk, cond_false, Nat.add_comm (a * (p - 1)), Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · unfold cB; rw [hk, cond_false, Nat.add_comm (a * (p - 1)), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The cover.** If all batches pass, every element is the product of the letters of some word. -/
theorem cover_of_batches [Fact p.Prime] [NeZero n] (P : Prm) (hv : P.valid) (hpP : P.p = p) (hnP : P.n = n)
    (hN : P.N = p * n) {ONES RD RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    (hRD : RD = pkF P.w (fun j => j / n) P.N) (hRZ : RZ = pkF P.w (fun j => j % n) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) (hrep : LetRep sG invAt P.Δ P.L lt)
    (hB : BatchesOK P ONES RD RZ lt) :
    ∀ x : G p n, ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧ wordG sG invAt dg P.L = x := by
  intro ⟨A, z⟩
  have h2 := p_two (p := p)
  have hw : 2 ≤ P.w := by have := hv.1; omega
  have hpw : p < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hpP]; nlinarith
  have hnw : n < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hnP]; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hzv := ZMod.val_lt (Multiplicative.toAdd z)
  have hdet := det_entries A
  -- the batch and the slot
  by_cases hc : A 1 0 = 0
  · obtain ⟨hs0, hs1, hs2⟩ := slotSL_nc A hc
    have ha1 := val_pos_of_ne (a_ne_of_c A hc)
    have hav := ZMod.val_lt (A 0 0)
    have hbv := ZMod.val_lt (A 0 1)
    obtain ⟨hbk, haB, hcB, hbl⟩ := bat_nc h2 ha1 hav
    obtain ⟨Dig, hDig⟩ := hB (p * (p - 1) + ((A 0 0).val - 1)) (by rw [hpP]; exact hbl)
    rw [hpP, hbk] at hDig
    simp only [cond_true] at hDig
    rw [haB, hcB, zero_mul] at hDig
    obtain ⟨j, hj⟩ : ∃ j, j = (A 0 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
    have hjN : j < P.N := by
      rw [hN]
      calc j < (A 0 1).val * n + n := by omega
        _ = ((A 0 1).val + 1) * n := by ring
        _ ≤ p * n := Nat.mul_le_mul_right _ hbv
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun j => j / n) (tc := fun _ => 0)
      (td := fun _ => 0) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) hRD h0 h0 hRZ
      (fun j hj' => ⟨by omega, by
        have : j / n < p := (Nat.div_lt_iff_lt_mul hn0).2 (by rw [← hN]; exact hj')
        omega, by positivity, by positivity, by
        have := Nat.mod_lt j hn0; omega⟩) hDig j hjN
    obtain ⟨hdg, ma, mc, mz, mb, -⟩ := this
    refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
    obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc mb
    rw [hnP] at mz
    have hja : j / n = (A 0 1).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
    have hjz : j % n = (Multiplicative.toAdd z).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
    have W00 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 0 = A 0 0 := by
      rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    have W01 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 1 = A 0 1 := by
      rw [← eb, cast_of_modEq (mb rfl), hja, ZMod.natCast_zmod_val]
    have W10 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 1 0 = A 1 0 := by
      rw [← ec, cast_of_modEq mc, hc, Nat.cast_zero]
    have Wz : Multiplicative.toAdd (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = Multiplicative.toAdd z := by
      rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
    have W11 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 1 1 = A 1 1 := by
      have hW := det_entries (wordG sG invAt (digit (fld P.w Dig j)) P.L).1
      rw [W00, W01, W10] at hW
      rw [hc, mul_zero, sub_zero] at hdet hW
      have : A 0 0 * ((wordG sG invAt (digit (fld P.w Dig j)) P.L).1 1 1 - A 1 1) = 0 := by
        rw [mul_sub, hW, hdet, sub_self]
      rcases mul_eq_zero.mp this with h0' | h0'
      · exact absurd h0' (a_ne_of_c A hc)
      · exact sub_eq_zero.mp h0'
    refine Prod.ext (SpecialLinearGroup.ext _ _ ?_) (Multiplicative.toAdd.injective Wz)
    intro i j'; fin_cases i <;> fin_cases j'
    exacts [W00, W01, W10, W11]
  · obtain ⟨hs0, hs1, hs2, hs3⟩ := slotSL_c A hc
    have hav := ZMod.val_lt (A 0 0)
    have hcv := ZMod.val_lt (A 1 0)
    have hdv := ZMod.val_lt (A 1 1)
    have hc1 := val_pos_of_ne hc
    obtain ⟨hbk, haB, hcB, hbl⟩ := bat_c h2 hav hc1 hcv
    obtain ⟨Dig, hDig⟩ := hB ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) (by rw [hpP]; exact hbl)
    rw [hpP, hbk] at hDig
    simp only [cond_false] at hDig
    rw [haB, hcB] at hDig
    obtain ⟨j, hj⟩ : ∃ j, j = (A 1 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
    have hjN : j < P.N := by
      rw [hN]
      calc j < (A 1 1).val * n + n := by omega
        _ = ((A 1 1).val + 1) * n := by ring
        _ ≤ p * n := Nat.mul_le_mul_right _ hdv
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun _ => 0) (tc := fun _ => (A 1 0).val)
      (td := fun j => j / n) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) h0 (by rw [hO, ← pkF_const])
      hRD hRZ
      (fun j hj' => ⟨by omega, by positivity, by omega, by
        have : j / n < p := (Nat.div_lt_iff_lt_mul hn0).2 (by rw [← hN]; exact hj')
        omega, by
        have := Nat.mod_lt j hn0; omega⟩) hDig j hjN
    obtain ⟨hdg, ma, mc, mz, -, md⟩ := this
    refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
    obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc md
    rw [hnP] at mz
    have hjd : j / n = (A 1 1).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
    have hjz : j % n = (Multiplicative.toAdd z).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
    have W00 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 0 = A 0 0 := by
      rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    have W10 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 1 0 = A 1 0 := by
      rw [← ec, cast_of_modEq mc, ZMod.natCast_zmod_val]
    have W11 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 1 1 = A 1 1 := by
      rw [← ed, cast_of_modEq (md rfl), hjd, ZMod.natCast_zmod_val]
    have Wz : Multiplicative.toAdd (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = Multiplicative.toAdd z := by
      rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
    have W01 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 1 = A 0 1 := by
      have hW := det_entries (wordG sG invAt (digit (fld P.w Dig j)) P.L).1
      rw [W00, W10, W11] at hW
      have : ((wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 1 - A 0 1) * A 1 0 = 0 := by
        have e1 : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 0 1 * A 1 0 = A 0 0 * A 1 1 - 1 := by
          linear_combination -hW
        have e2 : A 0 1 * A 1 0 = A 0 0 * A 1 1 - 1 := by linear_combination -hdet
        rw [sub_mul, e1, e2, sub_self]
      rcases mul_eq_zero.mp this with h0' | h0'
      · exact sub_eq_zero.mp h0'
      · exact absurd h0' hc
    refine Prod.ext (SpecialLinearGroup.ext _ _ ?_) (Multiplicative.toAdd.injective Wz)
    intro i j'; fin_cases i <;> fin_cases j'
    exacts [W00, W01, W10, W11]

/-! ## Word shapes and the record form -/

open BipartiteDD.Haar SimpleGraph

/-- Pairs of letters `(sG (dg (o + 2i)), sG (dg (o + 2i + 1)))` for `i < k`. -/
def pairsL (dg : ℕ → ℕ) (o : ℕ) : ℕ → List (G p n × G p n)
  | 0 => []
  | k + 1 => pairsL dg o k ++ [(sG (dg (o + 2 * k)), sG (dg (o + 2 * k + 1)))]

theorem pairsL_mem {S : Finset (G p n)} {Δ : ℕ} (hS : ∀ u < Δ, sG u ∈ S) (dg : ℕ → ℕ) (o : ℕ) :
    ∀ k, (∀ t < o + 2 * k, dg t < Δ) → ∀ q ∈ pairsL sG dg o k, q.1 ∈ S ∧ q.2 ∈ S := by
  intro k
  induction k with
  | zero => intro _ q hq; simp [pairsL] at hq
  | succ k ih =>
    intro hdg q hq
    simp only [pairsL, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact ih (fun t ht => hdg t (by omega)) q hq
    · exact ⟨hS _ (hdg _ (by omega)), hS _ (hdg _ (by omega))⟩

theorem pairsL_length (dg : ℕ → ℕ) (o : ℕ) : ∀ k, (pairsL sG dg o k).length = k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [pairsL, ih]

theorem word_left (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 0)) :
    ∀ k, wordG sG invAt dg (2 * k) = ((pairsL sG dg 0 k).map (fun q => q.1⁻¹ * q.2)).prod := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [wordG, pairsL, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ih, letterG, hinv, Nat.zero_add]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [h1, h2, mul_assoc]

theorem word_right (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 1)) :
    ∀ k, wordG sG invAt dg (2 * k) = ((pairsL sG dg 0 k).map (fun q => q.1 * q.2⁻¹)).prod := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [wordG, pairsL, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ih, letterG, hinv, Nat.zero_add]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [h1, h2, mul_assoc]

theorem word_even (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 1)) :
    ∀ k, wordG sG invAt dg (2 * k + 1) = sG (dg 0) * ((pairsL sG dg 1 k).map (fun q => q.1⁻¹ * q.2)).prod := by
  intro k
  induction k with
  | zero =>
    simp only [wordG, letterG, hinv, pairsL]
    simp
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [e, wordG_succ, wordG_succ, ih]
    have h1 : letterG sG invAt (2 * k + 1) (dg (2 * k + 1)) = (sG (dg (2 * k + 1)))⁻¹ := by
      simp only [letterG, hinv]; simp [show (2 * k + 1) % 2 = 1 by omega]
    have h2 : letterG sG invAt (2 * k + 1 + 1) (dg (2 * k + 1 + 1)) = sG (dg (2 * k + 1 + 1)) := by
      simp only [letterG, hinv]; simp [show (2 * k + 1 + 1) % 2 = 0 by omega]
    rw [h1, h2]
    simp only [pairsL, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [show 1 + 2 * k = 2 * k + 1 by ring, show 2 * k + 1 + 1 = 2 * k + 1 + 1 by rfl]
    simp only [mul_assoc]

/-- Transport of the diameter along an equivalence `G ⊕ G ≃ W`. -/
theorem ediam_transport {V W : Type*} (G' : SimpleGraph V) (H : SimpleGraph W) (e : V ≃ W)
    (hH : ∀ x y, H.Adj (e x) (e y) ↔ G'.Adj x y) {D : ℕ∞} (hG : G'.ediam ≤ D) : H.ediam ≤ D := by
  rw [ediam_le_iff] at hG ⊢
  intro w₁ w₂
  obtain ⟨u, rfl⟩ := e.surjective w₁
  obtain ⟨v, rfl⟩ := e.surjective w₂
  by_cases hr : G'.Reachable u v
  · obtain ⟨q, hq⟩ := hr.exists_walk_length_eq_edist
    let f : G' →g H := { toFun := e, map_rel' := fun h => (hH _ _).2 h }
    calc H.edist (e u) (e v) ≤ ((q.map f).length : ℕ∞) := edist_le _
      _ = G'.edist u v := by rw [Walk.length_map, hq]
      _ ≤ D := hG u v
  · have := hG u v
    rw [edist_eq_top_of_not_reachable hr] at this
    exact le_top.trans this

/-- The vertex numbering of the Haar graph: `G ⊕ G ≃ Fin (2 |G|)`. -/
noncomputable def haarEquiv (K : Type*) [Fintype K] : K ⊕ K ≃ Fin (2 * Fintype.card K) :=
  (Equiv.sumCongr (Fintype.equivFin K) (Fintype.equivFin K)).trans
    (finSumFinEquiv.trans (finCongr (by ring)))

/-- **The record form, odd diameter `2k + 1`.** -/
theorem record_odd {K : Type*} [Group K] [Fintype K] [DecidableEq K] (S : Finset K) (hS : S.Nonempty)
    (k : ℕ) (hA : ∀ x : K, IsLeftWord S k x) (hB : ∀ x : K, IsRightWord S k x) :
    ∃ H : SimpleGraph (Fin (2 * Fintype.card K)), BipartiteDD.IsBipartiteDegDiam H S.card (2 * k + 1) := by
  let e := haarEquiv K
  let H := (haarGraph S).comap e.symm
  have hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y := fun x y => by simp [H, comap_adj]
  refine ⟨H, colorable_of S H e hH, degree_of S H e hH, ?_⟩
  exact ediam_transport _ H e hH (haar_ediam_le_odd hS k hA hB)

/-- **The record form, even diameter `2k + 2`.** -/
theorem record_even {K : Type*} [Group K] [Fintype K] [DecidableEq K] (S : Finset K)
    (k : ℕ) (hA : ∀ x : K, ∃ s ∈ S, IsLeftWord S k (s⁻¹ * x)) :
    ∃ H : SimpleGraph (Fin (2 * Fintype.card K)), BipartiteDD.IsBipartiteDegDiam H S.card (2 * k + 2) := by
  let e := haarEquiv K
  let H := (haarGraph S).comap e.symm
  have hH : ∀ x y, H.Adj (e x) (e y) ↔ (haarGraph S).Adj x y := fun x y => by simp [H, comap_adj]
  refine ⟨H, colorable_of S H e hH, degree_of S H e hH, ?_⟩
  exact ediam_transport _ H e hH (haar_ediam_le_even k hA)

end BipartiteDD.LeanAll.HaarSL2
