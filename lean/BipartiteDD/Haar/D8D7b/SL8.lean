import BipartiteDD.Haar.D8D7b.GF8
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! The group `SL(2, 8)` of order 504, with a computable numbering of its elements by `Fin 504`.

Elements are matrices `[[a, b], [c, d]]` over `GF(8)` (the ring `F8` of `GF8.lean`) with `a d - b c = 1`,
multiplied as matrices. In characteristic 2 this is `a d + b c = 1`.

The numbering is the one of `research/lean-haarD/gen_d8D7b.py`: the 56 elements with `c = 0` come first
(`n = (a - 1) * 8 + b`, with `d = a⁻¹`), then the 448 with `c ≠ 0` (`n = 56 + ((c - 1) * 8 + a) * 8 + d`, with
`b = (a d + 1) / c`). `quad` is the inverse of `enc` on determinant 1 matrices; `quad_enc` and `enc_quad` check
this on all of them by computation. -/

namespace BipartiteDD.Haar.D8D7b.SL8

open BipartiteDD.Haar.D8D7b

/-- The matrices `[[a, b], [c, d]]` over `GF(8)` of determinant 1. -/
@[ext]
structure Grp where
  a : F8
  b : F8
  c : F8
  d : F8
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

/-- The inverses in `GF(8)`, as a table: `invTab[x] = x⁻¹` for `x ≠ 0`. -/
def invTab : List ℕ := [0, 1, 5, 6, 7, 2, 3, 4]

/-- The inverse of a nonzero element of `GF(8)`; `0` for `0`. -/
def invF (x : F8) : F8 := ofN (invTab.getD (toN x) 0)

/-- The index of the matrix `[[a, b], [c, d]]`, for `n < 504`: `(a - 1) * 8 + b` if `c = 0`, and
`56 + ((c - 1) * 8 + a) * 8 + d` otherwise. -/
def enc (a b c d : F8) : ℕ :=
  if c = zeroF then (toN a - 1) * 8 + toN b else 56 + ((toN c - 1) * 8 + toN a) * 8 + toN d

/-- The matrix with index `n`, for `n < 504`: the inverse of `enc` on determinant 1 matrices. -/
def quad (n : ℕ) : F8 × F8 × F8 × F8 :=
  if n < 56 then (ofN (n / 8 + 1), ofN (n % 8), zeroF, invF (ofN (n / 8 + 1)))
  else
    let a := ofN ((n - 56) / 8 % 8)
    let c := ofN ((n - 56) / 64 + 1)
    let d := ofN ((n - 56) % 8)
    (a, mulF (addF (mulF a d) oneF) (invF c), c, d)

theorem toN_lt (x : F8) : toN x < 8 := (x : Fin 8).isLt

theorem enc_lt (a b c d : F8) : enc a b c d < 504 := by
  unfold enc
  have := toN_lt a
  have := toN_lt b
  have := toN_lt c
  have := toN_lt d
  split <;> omega

/-- The determinant of `quad n` is `1`, for `n < 504`. -/
theorem det_quad : ∀ n < 504, (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 := by
  decide +kernel

/-- `quad` inverts `enc` on determinant 1 matrices. -/
theorem quad_enc : ∀ a b c d : F8, a * d - b * c = 1 → quad (enc a b c d) = (a, b, c, d) := by
  decide +kernel

/-- `enc` inverts `quad` on `n < 504`. -/
theorem enc_quad : ∀ n < 504, enc (quad n).1 (quad n).2.1 (quad n).2.2.1 (quad n).2.2.2 = n := by
  decide +kernel

/-- The element with index `n`, for `n < 504`; the identity for other `n`. -/
def grpOf (n : ℕ) : Grp :=
  if h : (quad n).1 * (quad n).2.2.2 - (quad n).2.1 * (quad n).2.2.1 = 1 then
    ⟨(quad n).1, (quad n).2.1, (quad n).2.2.1, (quad n).2.2.2, h⟩
  else 1

theorem enc_grp (g : Grp) : enc g.a g.b g.c g.d < 504 := enc_lt g.a g.b g.c g.d

theorem grpOf_enc (g : Grp) : grpOf (enc g.a g.b g.c g.d) = g := by
  have h := quad_enc g.a g.b g.c g.d g.det
  unfold grpOf
  rw [h]
  simp only [g.det, dite_true]

theorem grpOf_fields {n : ℕ} (hn : n < 504) :
    (grpOf n).a = (quad n).1 ∧ (grpOf n).b = (quad n).2.1 ∧
      (grpOf n).c = (quad n).2.2.1 ∧ (grpOf n).d = (quad n).2.2.2 := by
  unfold grpOf
  rw [dif_pos (det_quad n hn)]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The numbering of `SL(2, 8)`: `Grp ≃ Fin 504`. -/
def equiv504 : Grp ≃ Fin 504 where
  toFun g := ⟨enc g.a g.b g.c g.d, enc_lt g.a g.b g.c g.d⟩
  invFun n := grpOf n.1
  left_inv g := grpOf_enc g
  right_inv n := by
    apply Fin.ext
    obtain ⟨ha, hb, hc, hd⟩ := grpOf_fields n.2
    show enc (grpOf n.1).a (grpOf n.1).b (grpOf n.1).c (grpOf n.1).d = n.1
    rw [ha, hb, hc, hd]
    exact enc_quad n.1 n.2

end BipartiteDD.Haar.D8D7b.SL8
