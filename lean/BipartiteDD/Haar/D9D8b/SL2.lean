import BipartiteDD.Haar.D9D8b.GF27
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 27)` of order 19656, with a computable numbering by `ℕ`.

An element is a matrix `[[a, b], [c, d]]` over `GF(27)` of determinant `1`.

The numbering: the matrices with `c = 0` come first, `n = (a - 1) * 27 + b` for `a ∈ 1 … 26` (then `d = a⁻¹`),
then the ones with `c ≠ 0`, `n = 702 + ((c - 1) * 27 + a) * 27 + d` for `c ∈ 1 … 26` (then `b = (a d - 1) c⁻¹`). -/

namespace BipartiteDD.Haar.D9D8b

/-- The matrices `[[a, b], [c, d]]` over `GF(27)` of determinant `1`. -/
@[ext]
structure SL2 where
  a : F27
  b : F27
  c : F27
  d : F27
  det : a * d - b * c = 1
  deriving DecidableEq

instance : Mul SL2 :=
  ⟨fun g h => ⟨g.a * h.a + g.b * h.c, g.a * h.b + g.b * h.d, g.c * h.a + g.d * h.c, g.c * h.b + g.d * h.d,
    by linear_combination (h.a * h.d - h.b * h.c) * g.det + h.det⟩⟩

instance : One SL2 := ⟨⟨1, 0, 0, 1, by ring⟩⟩

instance : Inv SL2 := ⟨fun g => ⟨g.d, -g.b, -g.c, g.a, by linear_combination g.det⟩⟩

theorem mul_a (g h : SL2) : (g * h).a = g.a * h.a + g.b * h.c := rfl
theorem mul_b (g h : SL2) : (g * h).b = g.a * h.b + g.b * h.d := rfl
theorem mul_c (g h : SL2) : (g * h).c = g.c * h.a + g.d * h.c := rfl
theorem mul_d (g h : SL2) : (g * h).d = g.c * h.b + g.d * h.d := rfl
theorem one_a : (1 : SL2).a = 1 := rfl
theorem one_b : (1 : SL2).b = 0 := rfl
theorem one_c : (1 : SL2).c = 0 := rfl
theorem one_d : (1 : SL2).d = 1 := rfl
theorem inv_a (g : SL2) : (g⁻¹).a = g.d := rfl
theorem inv_b (g : SL2) : (g⁻¹).b = -g.b := rfl
theorem inv_c (g : SL2) : (g⁻¹).c = -g.c := rfl
theorem inv_d (g : SL2) : (g⁻¹).d = g.a := rfl

instance : Group SL2 where
  mul_assoc g h k := by
    refine SL2.ext ?_ ?_ ?_ ?_ <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> ring
  one_mul g := by
    refine SL2.ext ?_ ?_ ?_ ?_ <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d] <;> ring
  mul_one g := by
    refine SL2.ext ?_ ?_ ?_ ?_ <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d] <;> ring
  inv_mul_cancel g := by
    refine SL2.ext ?_ ?_ ?_ ?_ <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d, inv_a, inv_b, inv_c, inv_d]
    · linear_combination g.det
    · ring
    · ring
    · linear_combination g.det

/-! The numbering. -/

/-- The number of the matrix `[[a, b], [c, d]]`. -/
def encT (a b c d : F27) : ℕ :=
  if c = 0 then (a.val - 1) * 27 + b.val else 702 + ((c.val - 1) * 27 + a.val) * 27 + d.val

/-- The inverse in `GF(27)`. -/
def invF27 (x : F27) : F27 := invF x

theorem mul_invF27 (x : F27) (hx : x ≠ 0) : x * invF27 x = 1 := mul_invF x hx

theorem invF27_eq (x y : F27) (h : x * y = 1) : invF27 x = y := by
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact absurd h (by decide)
  linear_combination y * mul_invF27 x hx - invF27 x * h

theorem val_pos_fin : ∀ x : Fin 27, x ≠ 0 → 1 ≤ x.val := by
  decide +kernel

theorem F27.val_pos (x : F27) (hx : x ≠ 0) : 1 ≤ x.val := val_pos_fin x hx

/-- The matrix entries of the number `n`, for `n < 19656`. -/
def quad (n : ℕ) : F27 × F27 × F27 × F27 :=
  if n < 702 then
    (ofN (n / 27 + 1), ofN (n % 27), 0, invF27 (ofN (n / 27 + 1)))
  else
    (ofN ((n - 702) / 27 % 27),
      (ofN ((n - 702) / 27 % 27) * ofN ((n - 702) % 27) - 1) * invF27 (ofN ((n - 702) / 729 + 1)),
      ofN ((n - 702) / 729 + 1), ofN ((n - 702) % 27))

/-- The checks of `quad n`: the determinant is `1`, and `n` is the number of `quad n`. -/
def detB (n : ℕ) : Bool := decide ((quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1)

/-- See `detB`. -/
def encB (n : ℕ) : Bool :=
  decide (encT (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n)

/-- The checks of the indices `lo ≤ n < lo + len`, as one Boolean (packed to keep each kernel run small). -/
def chkQ (lo len : ℕ) : Bool := (List.range len).all (fun i => detB (lo + i) && encB (lo + i))

set_option maxRecDepth 100000 in
theorem chkQ_0 : chkQ 0 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_1 : chkQ 2000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_2 : chkQ 4000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_3 : chkQ 6000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_4 : chkQ 8000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_5 : chkQ 10000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_6 : chkQ 12000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_7 : chkQ 14000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_8 : chkQ 16000 2000 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem chkQ_9 : chkQ 18000 1656 = true := by decide +kernel

theorem chk_mem (lo len : ℕ) (h : chkQ lo len = true) (n : ℕ) (h1 : lo ≤ n) (h2 : n < lo + len) :
    (detB n && encB n) = true := by
  have := List.all_eq_true.mp h (n - lo) (List.mem_range.mpr (by omega))
  rwa [show lo + (n - lo) = n by omega] at this

theorem quad_ok (n : ℕ) (hn : n < 19656) : (detB n && encB n) = true := by
  rcases (show n / 2000 = 0 ∨ n / 2000 = 1 ∨ n / 2000 = 2 ∨ n / 2000 = 3 ∨ n / 2000 = 4 ∨ n / 2000 = 5 ∨
      n / 2000 = 6 ∨ n / 2000 = 7 ∨ n / 2000 = 8 ∨ n / 2000 = 9 by omega) with
    h | h | h | h | h | h | h | h | h | h
  · exact chk_mem 0 2000 chkQ_0 n (by omega) (by omega)
  · exact chk_mem 2000 2000 chkQ_1 n (by omega) (by omega)
  · exact chk_mem 4000 2000 chkQ_2 n (by omega) (by omega)
  · exact chk_mem 6000 2000 chkQ_3 n (by omega) (by omega)
  · exact chk_mem 8000 2000 chkQ_4 n (by omega) (by omega)
  · exact chk_mem 10000 2000 chkQ_5 n (by omega) (by omega)
  · exact chk_mem 12000 2000 chkQ_6 n (by omega) (by omega)
  · exact chk_mem 14000 2000 chkQ_7 n (by omega) (by omega)
  · exact chk_mem 16000 2000 chkQ_8 n (by omega) (by omega)
  · exact chk_mem 18000 1656 chkQ_9 n (by omega) (by omega)

/-- The entries of `quad n` have determinant `1`, for `n < 19656`. -/
theorem quad_det_all (n : ℕ) (hn : n < 19656) :
    (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  have h := quad_ok n hn
  simp only [Bool.and_eq_true, detB, encB, decide_eq_true_eq] at h
  exact h.1

/-- The number of `quad n`, for `n < 19656`. -/
theorem encT_quad_all (n : ℕ) (hn : n < 19656) :
    encT (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  have h := quad_ok n hn
  simp only [Bool.and_eq_true, detB, encB, decide_eq_true_eq] at h
  exact h.2

theorem encT_lt (a b c d : F27) (h : a * d - b * c = 1) : encT a b c d < 19656 := by
  unfold encT
  split_ifs with hc
  · have ha : a ≠ 0 := by
      rintro rfl
      rw [hc, zero_mul, mul_zero, sub_zero] at h
      exact absurd h (by decide)
    have := F27.val_pos a ha
    have := F27.val_lt a
    have := F27.val_lt b
    omega
  · have := F27.val_pos c hc
    have := F27.val_lt c
    have := F27.val_lt a
    have := F27.val_lt d
    omega

theorem quad_encT (a b c d : F27) (h : a * d - b * c = 1) :
    quad (encT a b c d) = (a, b, c, d) := by
  unfold encT
  split_ifs with hc
  · subst hc
    have ha : a ≠ 0 := by
      rintro rfl
      rw [zero_mul, mul_zero, sub_zero] at h
      exact absurd h (by decide)
    have hd : a * d = 1 := by linear_combination h
    have hav := F27.val_pos a ha
    have hav' := F27.val_lt a
    have hbv := F27.val_lt b
    have hn : (a.val - 1) * 27 + b.val < 702 := by omega
    have e1 : ((a.val - 1) * 27 + b.val) / 27 + 1 = a.val := by omega
    have e2 : ((a.val - 1) * 27 + b.val) % 27 = b.val := by omega
    unfold quad
    rw [if_pos hn, e1, e2]
    simp only [ofN_val, invF27_eq a d hd]
  · have hcv := F27.val_pos c hc
    have hcv' := F27.val_lt c
    have hav' := F27.val_lt a
    have hdv' := F27.val_lt d
    have hn : ¬ (702 + ((c.val - 1) * 27 + a.val) * 27 + d.val < 702) := by omega
    have e1 : (702 + ((c.val - 1) * 27 + a.val) * 27 + d.val - 702) / 27 % 27 = a.val := by omega
    have e2 : (702 + ((c.val - 1) * 27 + a.val) * 27 + d.val - 702) % 27 = d.val := by omega
    have e3 : (702 + ((c.val - 1) * 27 + a.val) * 27 + d.val - 702) / 729 + 1 = c.val := by omega
    have hb : (a * d - 1) * invF27 c = b := by
      have hinv : c * invF27 c = 1 := mul_invF27 c hc
      have hbc : a * d - 1 = b * c := by linear_combination h
      rw [hbc]
      linear_combination b * hinv
    unfold quad
    rw [if_neg hn, e1, e2, e3]
    simp only [ofN_val, hb]

/-- The matrix with number `n`, for `n < 19656`. -/
def grpP (n : ℕ) : SL2 :=
  if h : n < 19656 then ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, by
    have := quad_det_all n h
    exact this⟩ else 1

/-- The number of a matrix. -/
def enc (g : SL2) : ℕ := encT g.a g.b g.c g.d

theorem enc_lt (g : SL2) : enc g < 19656 := encT_lt g.a g.b g.c g.d g.det

theorem grpP_enc (g : SL2) : grpP (enc g) = g := by
  unfold grpP
  rw [dif_pos (enc_lt g)]
  have hq : quad (enc g) = (g.a, g.b, g.c, g.d) := quad_encT g.a g.b g.c g.d g.det
  have hq' : (quad (enc g)).1 = g.a ∧ (quad (enc g)).2.1 = g.b ∧ (quad (enc g)).2.2.1 = g.c ∧
      (quad (enc g)).2.2.2 = g.d := by
    rw [hq]
    exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := hq'
  exact SL2.ext h1 h2 h3 h4

theorem enc_grpP (n : ℕ) (hn : n < 19656) : enc (grpP n) = n := by
  unfold grpP
  rw [dif_pos hn]
  exact encT_quad_all n hn

end BipartiteDD.Haar.D9D8b
