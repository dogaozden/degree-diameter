import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 19)` of order 6840, with a computable numbering of its elements by `Fin 6840`.

Elements are matrices `[[a, b], [c, d]]` over `ZMod 19` with `a * d - b * c = 1`, multiplied as
matrices. The numbering is the one of `research/lean-haarD/gen_d8D7.py`: the 342 elements with `c = 0`
come first (`n = (a - 1) * 19 + b`), then the 6498 with `c ≠ 0` (`n = 342 + ((c - 1) * 19 + a) * 19 + d`).
`quad` is the inverse of `enc` on determinant 1 matrices; `quad_enc` and `enc_quad` check this on
all of them by computation. -/

namespace BipartiteDD.Haar.SL19

/-- The matrices `[[a, b], [c, d]]` over `ZMod 19` of determinant 1. -/
@[ext]
structure Grp where
  a : ZMod 19
  b : ZMod 19
  c : ZMod 19
  d : ZMod 19
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

/-- The inverses in `ZMod 19`, as a table: `invTab[x] = x⁻¹` for `x ≠ 0`. -/
def invTab : List (ZMod 19) :=
  [0, 1, 10, 13, 5, 4, 16, 11, 12, 17, 2, 7, 8, 3, 15, 14, 6, 9, 18]

/-- Inverses in `ZMod 19`: `inv19 x = x⁻¹` for `x ≠ 0`. -/
def inv19 (x : ZMod 19) : ZMod 19 := invTab.getD x.val 0

theorem inv19_spec : ∀ x : ZMod 19, x ≠ 0 → x * inv19 x = 1 := by
  decide +kernel

/-- The matrix entries `(a, b, c, d)` of the element with index `n`, for `n < 6840`. -/
def quad (n : ℕ) : ZMod 19 × ZMod 19 × ZMod 19 × ZMod 19 :=
  if n < 342 then
    (((n / 19 + 1 : ℕ) : ZMod 19), ((n % 19 : ℕ) : ZMod 19), 0,
      inv19 ((n / 19 + 1 : ℕ) : ZMod 19))
  else
    let m := n - 342
    let a : ZMod 19 := ((m / 19 % 19 : ℕ) : ZMod 19)
    let c : ZMod 19 := ((m / 361 + 1 : ℕ) : ZMod 19)
    let d : ZMod 19 := ((m % 19 : ℕ) : ZMod 19)
    (a, (a * d - 1) * inv19 c, c, d)

/-- The index of the matrix `[[a, b], [c, d]]`. -/
def enc (a b c d : ZMod 19) : ℕ :=
  if c = 0 then (a.val - 1) * 19 + b.val else 342 + ((c.val - 1) * 19 + a.val) * 19 + d.val

theorem enc_bound (a b c d : ZMod 19) : enc a b c d < 6840 := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have hd := ZMod.val_lt d
  unfold enc
  split_ifs <;> omega

/-- The `c = 0` case of `quad_enc`: `a * d = 1` forces `d = a⁻¹`. Checked on the 6859 triples. -/
theorem quad_enc0 : ∀ a b d : ZMod 19, a * d = 1 → quad ((a.val - 1) * 19 + b.val) = (a, b, 0, d) := by
  decide +kernel

/-- The `c ≠ 0` case of `quad_enc`, with `b` written as `(a d - 1) c⁻¹`. Checked on the 6859 triples. -/
theorem quad_enc1 : ∀ a c d : ZMod 19, c ≠ 0 →
    quad (342 + ((c.val - 1) * 19 + a.val) * 19 + d.val) = (a, (a * d - 1) * inv19 c, c, d) := by
  decide +kernel

theorem quad_enc (a b c d : ZMod 19) (h : a * d - b * c = 1) : quad (enc a b c d) = (a, b, c, d) := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have hn : enc a b 0 d = (a.val - 1) * 19 + b.val := by simp [enc]
    rw [hn, quad_enc0 a b d had]
  · have hb : b = (a * d - 1) * inv19 c := by
      have hi := inv19_spec c hc
      linear_combination (-(inv19 c)) * h - b * hi
    have hn : enc a b c d = 342 + ((c.val - 1) * 19 + a.val) * 19 + d.val := by simp [enc, hc]
    rw [hn, quad_enc1 a c d hc, hb]

set_option maxRecDepth 100000 in
theorem det_quad_all : (List.range 6840).all (fun n =>
    decide ((quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem enc_quad_all : (List.range 6840).all (fun n =>
    decide (enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n)) = true := by
  decide +kernel

theorem det_quad : ∀ n < 6840, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  intro n hn
  have h := List.all_eq_true.mp det_quad_all n (List.mem_range.mpr hn)
  simpa using h

theorem enc_quad : ∀ n < 6840,
    enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  intro n hn
  have h := List.all_eq_true.mp enc_quad_all n (List.mem_range.mpr hn)
  simpa using h

/-- The element with index `n`, for `n < 6840`; the identity for other `n`. -/
def grpOf (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h⟩
  else 1

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 6840 :=
  enc_bound g.a g.b g.c g.d

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  simp only [grpOf, quad_enc g.a g.b g.c g.d g.det]
  rw [dif_pos g.det]

theorem grpOf_fields {n : ℕ} (hn : n < 6840) :
    (grpOf n).a = (quad n).1 ∧ (grpOf n).b = (quad n).2.1 ∧
      (grpOf n).c = (quad n).2.2.1 ∧ (grpOf n).d = (quad n).2.2.2 := by
  unfold grpOf
  rw [dif_pos (det_quad n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The numbering of `SL(2, 19)`: `Grp ≃ Fin 6840`. -/
def equiv6840 : Grp ≃ Fin 6840 where
  toFun g := ⟨enc g.a g.b g.c g.d, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    obtain ⟨ha, hb, hc, hd⟩ := grpOf_fields n.2
    show enc (grpOf n.1).a (grpOf n.1).b (grpOf n.1).c (grpOf n.1).d = n.1
    rw [ha, hb, hc, hd]
    exact enc_quad n.1 n.2

end BipartiteDD.Haar.SL19
