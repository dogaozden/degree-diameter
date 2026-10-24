import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 17)` of order 4896, with a computable numbering of its elements by `Fin 4896`.

Elements are matrices `[[a, b], [c, d]]` over `ZMod 17` with `a * d - b * c = 1`, multiplied as
matrices. The numbering is the one of `research/lean-haarD/gen_d6D9c.py`: the 272 elements with `c = 0`
come first (`n = (a - 1) * 17 + b`), then the 4624 with `c ≠ 0` (`n = 272 + ((c - 1) * 17 + a) * 17 + d`).
`quad` is the inverse of `enc` on determinant 1 matrices; `quad_enc` and `enc_quad` check this on
all of them by computation. -/

namespace BipartiteDD.Haar.D6D9c.SL17

/-- The matrices `[[a, b], [c, d]]` over `ZMod 17` of determinant 1. -/
@[ext]
structure Grp where
  a : ZMod 17
  b : ZMod 17
  c : ZMod 17
  d : ZMod 17
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

/-- The inverses in `ZMod 17`, as a table: `invTab[x] = x⁻¹` for `x ≠ 0`. -/
def invTab : List (ZMod 17) :=
  [0, 1, 9, 6, 13, 7, 3, 5, 15, 2, 12, 14, 10, 4, 11, 8, 16]

/-- Inverses in `ZMod 17`: `inv17 x = x⁻¹` for `x ≠ 0`. -/
def inv17 (x : ZMod 17) : ZMod 17 := invTab.getD x.val 0

theorem inv17_spec : ∀ x : ZMod 17, x ≠ 0 → x * inv17 x = 1 := by
  decide +kernel

/-- The matrix entries `(a, b, c, d)` of the element with index `n`, for `n < 4896`. -/
def quad (n : ℕ) : ZMod 17 × ZMod 17 × ZMod 17 × ZMod 17 :=
  if n < 272 then
    (((n / 17 + 1 : ℕ) : ZMod 17), ((n % 17 : ℕ) : ZMod 17), 0,
      inv17 ((n / 17 + 1 : ℕ) : ZMod 17))
  else
    let m := n - 272
    let a : ZMod 17 := ((m / 17 % 17 : ℕ) : ZMod 17)
    let c : ZMod 17 := ((m / 289 + 1 : ℕ) : ZMod 17)
    let d : ZMod 17 := ((m % 17 : ℕ) : ZMod 17)
    (a, (a * d - 1) * inv17 c, c, d)

/-- The index of the matrix `[[a, b], [c, d]]`. -/
def enc (a b c d : ZMod 17) : ℕ :=
  if c = 0 then (a.val - 1) * 17 + b.val else 272 + ((c.val - 1) * 17 + a.val) * 17 + d.val

theorem enc_bound (a b c d : ZMod 17) : enc a b c d < 4896 := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hc := ZMod.val_lt c
  have hd := ZMod.val_lt d
  unfold enc
  split_ifs <;> omega

/-- The `c = 0` case of `quad_enc`: `a * d = 1` forces `d = a⁻¹`. Checked on the 4913 triples. -/
theorem quad_enc0 : ∀ a b d : ZMod 17, a * d = 1 → quad ((a.val - 1) * 17 + b.val) = (a, b, 0, d) := by
  decide +kernel

/-- The `c ≠ 0` case of `quad_enc`, with `b` written as `(a d - 1) c⁻¹`. Checked on the 4913 triples. -/
theorem quad_enc1 : ∀ a c d : ZMod 17, c ≠ 0 →
    quad (272 + ((c.val - 1) * 17 + a.val) * 17 + d.val) = (a, (a * d - 1) * inv17 c, c, d) := by
  decide +kernel

theorem quad_enc (a b c d : ZMod 17) (h : a * d - b * c = 1) : quad (enc a b c d) = (a, b, c, d) := by
  by_cases hc : c = 0
  · subst hc
    have had : a * d = 1 := by simpa using h
    have hn : enc a b 0 d = (a.val - 1) * 17 + b.val := by simp [enc]
    rw [hn, quad_enc0 a b d had]
  · have hb : b = (a * d - 1) * inv17 c := by
      have hi := inv17_spec c hc
      linear_combination (-(inv17 c)) * h - b * hi
    have hn : enc a b c d = 272 + ((c.val - 1) * 17 + a.val) * 17 + d.val := by simp [enc, hc]
    rw [hn, quad_enc1 a c d hc, hb]

set_option maxRecDepth 100000 in
theorem det_quad_all : (List.range 4896).all (fun n =>
    decide ((quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem enc_quad_all : (List.range 4896).all (fun n =>
    decide (enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n)) = true := by
  decide +kernel

theorem det_quad : ∀ n < 4896, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  intro n hn
  have h := List.all_eq_true.mp det_quad_all n (List.mem_range.mpr hn)
  simpa using h

theorem enc_quad : ∀ n < 4896,
    enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  intro n hn
  have h := List.all_eq_true.mp enc_quad_all n (List.mem_range.mpr hn)
  simpa using h

/-- The element with index `n`, for `n < 4896`; the identity for other `n`. -/
def grpOf (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h⟩
  else 1

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 4896 :=
  enc_bound g.a g.b g.c g.d

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  simp only [grpOf, quad_enc g.a g.b g.c g.d g.det]
  rw [dif_pos g.det]

theorem grpOf_fields {n : ℕ} (hn : n < 4896) :
    (grpOf n).a = (quad n).1 ∧ (grpOf n).b = (quad n).2.1 ∧
      (grpOf n).c = (quad n).2.2.1 ∧ (grpOf n).d = (quad n).2.2.2 := by
  unfold grpOf
  rw [dif_pos (det_quad n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The numbering of `SL(2, 17)`: `Grp ≃ Fin 4896`. -/
def equiv4896 : Grp ≃ Fin 4896 where
  toFun g := ⟨enc g.a g.b g.c g.d, enc_lt g⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    obtain ⟨ha, hb, hc, hd⟩ := grpOf_fields n.2
    show enc (grpOf n.1).a (grpOf n.1).b (grpOf n.1).c (grpOf n.1).d = n.1
    rw [ha, hb, hc, hd]
    exact enc_quad n.1 n.2

end BipartiteDD.Haar.D6D9c.SL17
