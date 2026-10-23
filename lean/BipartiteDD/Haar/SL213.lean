import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 13)` of order 2184, with a computable numbering of its elements by `ℕ`.

Elements are matrices `[[a, b], [c, d]]` over `ZMod 13` with `a * d - b * c = 1`, multiplied as
matrices. The numbering is the one of `SL211.lean`, with 13 in place of 11: the 156 elements with
`c = 0` come first (`n = (a - 1) * 13 + b`), then the 2028 with `c ≠ 0`
(`n = 156 + ((c - 1) * 13 + a) * 13 + d`). `quad` is the inverse of `enc` on determinant 1 matrices;
`quad_enc`, `enc_quad` and the other lemmas check this on all of them by computation. -/

namespace BipartiteDD.Haar.SL213

/-- The matrices `[[a, b], [c, d]]` over `ZMod 13` of determinant 1. -/
@[ext]
structure Grp where
  a : ZMod 13
  b : ZMod 13
  c : ZMod 13
  d : ZMod 13
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

/-- The inverses in `ZMod 13`, as a table: `invTab[x] = x⁻¹` for `x ≠ 0`. -/
def invTab : List (ZMod 13) := [0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12]

/-- Inverses in `ZMod 13`: `inv13 x = x⁻¹` for `x ≠ 0`. -/
def inv13 (x : ZMod 13) : ZMod 13 := invTab.getD x.val 0

/-- The matrix entries `(a, b, c, d)` of the element with index `n`, for `n < 2184`. -/
def quad (n : ℕ) : ZMod 13 × ZMod 13 × ZMod 13 × ZMod 13 :=
  if n < 156 then
    (((n / 13 + 1 : ℕ) : ZMod 13), ((n % 13 : ℕ) : ZMod 13), 0,
      inv13 ((n / 13 + 1 : ℕ) : ZMod 13))
  else
    let m := n - 156
    let a : ZMod 13 := ((m / 13 % 13 : ℕ) : ZMod 13)
    let c : ZMod 13 := ((m / 169 + 1 : ℕ) : ZMod 13)
    let d : ZMod 13 := ((m % 13 : ℕ) : ZMod 13)
    (a, (a * d - 1) * inv13 c, c, d)

/-- The index of the matrix `[[a, b], [c, d]]`. -/
def enc (a b c d : ZMod 13) : ℕ :=
  if c = 0 then (a.val - 1) * 13 + b.val else 156 + ((c.val - 1) * 13 + a.val) * 13 + d.val

theorem enc_bound : ∀ a b c d : ZMod 13, a * d - b * c = 1 → enc a b c d < 2184 := by
  decide +kernel

theorem quad_enc : ∀ a b c d : ZMod 13, a * d - b * c = 1 → quad (enc a b c d) = (a, b, c, d) := by
  decide +kernel

theorem det_quad : ∀ n < 2184, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  decide +kernel

theorem enc_quad : ∀ n < 2184,
    enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  decide +kernel

/-- The element with index `n`, for `n < 2184`; the identity for other `n`. -/
def grpOf (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h⟩
  else 1

theorem enc_lt (g : Grp) : enc g.a g.b g.c g.d < 2184 :=
  enc_bound g.a g.b g.c g.d g.det

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  simp only [grpOf, quad_enc g.a g.b g.c g.d g.det]
  rw [dif_pos g.det]

theorem grpOf_fields {n : ℕ} (hn : n < 2184) :
    (grpOf n).a = (quad n).1 ∧ (grpOf n).b = (quad n).2.1 ∧
      (grpOf n).c = (quad n).2.2.1 ∧ (grpOf n).d = (quad n).2.2.2 := by
  unfold grpOf
  rw [dif_pos (det_quad n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem enc_grpOf {n : ℕ} (hn : n < 2184) :
    enc (grpOf n).a (grpOf n).b (grpOf n).c (grpOf n).d = n := by
  obtain ⟨ha, hb, hc, hd⟩ := grpOf_fields hn
  rw [ha, hb, hc, hd]
  exact enc_quad n hn

end BipartiteDD.Haar.SL213
