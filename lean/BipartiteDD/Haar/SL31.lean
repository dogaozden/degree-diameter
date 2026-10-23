import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 31)` of order 29760, with a computable numbering of its elements by `Fin 29760`.

Elements are matrices `[[a, b], [c, d]]` over `ZMod 31` with `a * d - b * c = 1`, multiplied as
matrices. The numbering is the one of `research/lean-haarD/gen_d7D9.py`: the 930 elements with `c = 0`
come first (`n = (a - 1) * 31 + b`), then the 28830 with `c ≠ 0` (`n = 930 + ((c - 1) * 31 + a) * 31 + d`).
`quad` is the inverse of `enc` on determinant 1 matrices; `quad_enc` and `enc_quad` check this on
all of them by computation. -/

namespace BipartiteDD.Haar.SL31

/-- The matrices `[[a, b], [c, d]]` over `ZMod 31` of determinant 1. -/
@[ext]
structure Grp where
  a : ZMod 31
  b : ZMod 31
  c : ZMod 31
  d : ZMod 31
  det : a * d - b * c = 1
  deriving DecidableEq

instance : Mul Grp :=
  ⟨fun g h => ⟨g.a * h.a + g.b * h.c, g.a * h.b + g.b * h.d, g.c * h.a + g.d * h.c,
    g.c * h.b + g.d * h.d, by linear_combination (g.a * g.d - g.b * g.c) * h.det + g.det⟩⟩

instance : One Grp := ⟨⟨1, 0, 0, 1, by ring⟩⟩

instance : Inv Grp := ⟨fun g => ⟨g.d, -g.b, -g.c, g.a, by linear_combination g.det⟩⟩

theorem mul_a (g h : Grp) : (g * h).a = g.a * h.a + g.b * h.c := rfl
theorem mul_b (g h : Grp) : (g * h).b = g.a * h.b + g.b * h.d := rfl
theorem mul_c (g h : Grp) : (g * h).c = g.c * h.a + g.d * h.c := rfl
theorem mul_d (g h : Grp) : (g * h).d = g.c * h.b + g.d * h.d := rfl
theorem one_a : (1 : Grp).a = 1 := rfl
theorem one_b : (1 : Grp).b = 0 := rfl
theorem one_c : (1 : Grp).c = 0 := rfl
theorem one_d : (1 : Grp).d = 1 := rfl
theorem inv_a (g : Grp) : (g⁻¹).a = g.d := rfl
theorem inv_b (g : Grp) : (g⁻¹).b = -g.b := rfl
theorem inv_c (g : Grp) : (g⁻¹).c = -g.c := rfl
theorem inv_d (g : Grp) : (g⁻¹).d = g.a := rfl

instance : Group Grp where
  mul_assoc g h k := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d] <;> ring
  one_mul g := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d] <;> ring
  mul_one g := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, one_a, one_b, one_c, one_d] <;> ring
  inv_mul_cancel g := by
    ext <;> simp only [mul_a, mul_b, mul_c, mul_d, inv_a, inv_b, inv_c, inv_d, one_a, one_b, one_c,
      one_d] <;> first | linear_combination g.det | ring

/-- The inverses in `ZMod 31`, as a table: `invTab[x] = x⁻¹` for `x ≠ 0`. -/
def invTab : List (ZMod 31) :=
  [0, 1, 16, 21, 8, 25, 26, 9, 4, 7, 28, 17, 13, 12, 20, 29, 2, 11, 19, 18, 14, 3, 24, 27, 22, 5, 6, 23,
    10, 15, 30]

/-- Inverses in `ZMod 31`: `inv31 x = x⁻¹` for `x ≠ 0`. -/
def inv31 (x : ZMod 31) : ZMod 31 := invTab.getD x.val 0

theorem inv31_spec : ∀ x : ZMod 31, x ≠ 0 → x * inv31 x = 1 := by
  decide +kernel

/-- The matrix entries `(a, b, c, d)` of the element with index `n`, for `n < 29760`. -/
def quad (n : ℕ) : ZMod 31 × ZMod 31 × ZMod 31 × ZMod 31 :=
  if n < 930 then
    (((n / 31 + 1 : ℕ) : ZMod 31), ((n % 31 : ℕ) : ZMod 31), 0,
      inv31 ((n / 31 + 1 : ℕ) : ZMod 31))
  else
    let m := n - 930
    let a : ZMod 31 := ((m / 31 % 31 : ℕ) : ZMod 31)
    let c : ZMod 31 := ((m / 961 + 1 : ℕ) : ZMod 31)
    let d : ZMod 31 := ((m % 31 : ℕ) : ZMod 31)
    (a, (a * d - 1) * inv31 c, c, d)

/-- The index of the matrix `[[a, b], [c, d]]`. -/
def enc (a b c d : ZMod 31) : ℕ :=
  if c = 0 then (a.val - 1) * 31 + b.val else 930 + ((c.val - 1) * 31 + a.val) * 31 + d.val

theorem enc_bound (a b c d : ZMod 31) : enc a b c d < 29760 := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have hd := ZMod.val_lt d
  unfold enc
  split_ifs <;> omega

/-- The `c = 0` case of `quad_enc`: `a * d = 1` forces `d = a⁻¹`. Checked on the 29791 triples. -/
theorem quad_enc0 : ∀ a b d : ZMod 31, a * d = 1 → quad ((a.val - 1) * 31 + b.val) = (a, b, 0, d) := by
  decide +kernel

/-- The `c ≠ 0` case of `quad_enc`, with `b` written as `(a d - 1) c⁻¹`. Checked on the 29791 triples. -/
theorem quad_enc1 : ∀ a c d : ZMod 31, c ≠ 0 →
    quad (930 + ((c.val - 1) * 31 + a.val) * 31 + d.val) = (a, (a * d - 1) * inv31 c, c, d) := by
  decide +kernel

theorem quad_enc (a b c d : ZMod 31) (h : a * d - b * c = 1) : quad (enc a b c d) = (a, b, c, d) := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have hn : enc a b 0 d = (a.val - 1) * 31 + b.val := by simp [enc]
    rw [hn, quad_enc0 a b d had]
  · have hb : b = (a * d - 1) * inv31 c := by
      have hi := inv31_spec c hc
      linear_combination (-(inv31 c)) * h - b * hi
    have hn : enc a b c d = 930 + ((c.val - 1) * 31 + a.val) * 31 + d.val := by simp [enc, hc]
    rw [hn, quad_enc1 a c d hc, hb]

set_option maxRecDepth 100000 in
theorem det_quad_all : (List.range 29760).all (fun n =>
    decide ((quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem enc_quad_all : (List.range 29760).all (fun n =>
    decide (enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n)) = true := by
  decide +kernel

theorem det_quad : ∀ n < 29760, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  intro n hn
  have h := List.all_eq_true.mp det_quad_all n (List.mem_range.mpr hn)
  simpa using h

theorem enc_quad : ∀ n < 29760,
    enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  intro n hn
  have h := List.all_eq_true.mp enc_quad_all n (List.mem_range.mpr hn)
  simpa using h

/-- The element with index `n`, for `n < 29760`; the identity for other `n`. -/
def grpOf (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h⟩
  else 1

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 29760 :=
  enc_bound g.a g.b g.c g.d

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  simp only [grpOf, quad_enc g.a g.b g.c g.d g.det]
  rw [dif_pos g.det]

theorem grpOf_fields {n : ℕ} (hn : n < 29760) :
    (grpOf n).a = (quad n).1 ∧ (grpOf n).b = (quad n).2.1 ∧
      (grpOf n).c = (quad n).2.2.1 ∧ (grpOf n).d = (quad n).2.2.2 := by
  unfold grpOf
  rw [dif_pos (det_quad n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The numbering of `SL(2, 31)`: `Grp ≃ Fin 29760`. -/
def equiv29760 : Grp ≃ Fin 29760 where
  toFun g := ⟨enc g.a g.b g.c g.d, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    obtain ⟨ha, hb, hc, hd⟩ := grpOf_fields n.2
    show enc (grpOf n.1).a (grpOf n.1).b (grpOf n.1).c (grpOf n.1).d = n.1
    rw [ha, hb, hc, hd]
    exact enc_quad n.1 n.2

end BipartiteDD.Haar.SL31
