import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_844 ⋊ Z_5` of the (6,7) record on 8440 vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod 844` and `y ∈ ZMod 5`, with product
`(x, y) * (x', y') = (x + 477 ^ y.val * x', y + y')`. This is the `meta 844 5 477` group of
`research/frontier/haar_gen3.c`, whose rule is `(a,j)(b,l) = (a + r^j b, j + l)` with `r = 477`.
The map `y ↦ 477 ^ y.val` is a homomorphism `ZMod 5 → ZMod 844` because `477 ^ 5 = 1` in `ZMod 844`;
`tw_add` checks this on all 25 pairs.

The index of `(x, y)` is `x.val * 5 + y.val`, the index `a * 5 + j` of `haar_gen3.c`. -/

namespace BipartiteDD.Haar.Meta844

/-- The twist `477 ^ y` for `y : ZMod 5`. -/
def tw (y : ZMod 5) : ZMod 844 := 477 ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod 5, tw (y + z) = tw y * tw z := by decide +kernel

/-- Elements of `Z_844 ⋊ Z_5`. -/
@[ext] structure Grp where
  x : ZMod 844
  y : ZMod 5
  deriving DecidableEq

instance : Group Grp where
  mul p q := ⟨p.x + tw p.y * q.x, p.y + q.y⟩
  one := ⟨0, 0⟩
  inv p := ⟨-(tw (-p.y) * p.x), -p.y⟩
  mul_assoc a b c := by
    ext
    · show a.x + tw a.y * b.x + tw (a.y + b.y) * c.x = a.x + tw a.y * (b.x + tw b.y * c.x)
      rw [tw_add]
      ring
    · show a.y + b.y + c.y = a.y + (b.y + c.y)
      exact add_assoc _ _ _
  one_mul a := by
    ext
    · show 0 + tw 0 * a.x = a.x
      rw [tw_zero]
      ring
    · show 0 + a.y = a.y
      exact zero_add _
  mul_one a := by
    ext
    · show a.x + tw a.y * 0 = a.x
      ring
    · show a.y + 0 = a.y
      exact add_zero _
  inv_mul_cancel a := by
    ext
    · show -(tw (-a.y) * a.x) + tw (-a.y) * a.x = 0
      ring
    · show -a.y + a.y = 0
      exact neg_add_cancel _

/-- The index of an element: `x.val * 5 + y.val`, in `[0, 4220)`. -/
def enc (g : Grp) : ℕ := g.x.val * 5 + g.y.val

/-- The element with index `n`: `(n / 5, n % 5)`. Inverse to `enc` on `n < 4220`. -/
def grpOf (n : ℕ) : Grp := ⟨(n / 5 : ℕ), (n % 5 : ℕ)⟩

theorem enc_lt (g : Grp) : enc g < 4220 := by
  have h1 := ZMod.val_lt g.x
  have h2 := ZMod.val_lt g.y
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt g.y
  have hd : (g.x.val * 5 + g.y.val) / 5 = g.x.val := by omega
  have hm : (g.x.val * 5 + g.y.val) % 5 = g.y.val := by omega
  unfold grpOf enc
  rw [hd, hm, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem enc_grpOf {n : ℕ} (hn : n < 4220) : enc (grpOf n) = n := by
  unfold enc grpOf
  have h1 : (n / 5 : ℕ) = (n / 5) % 844 := (Nat.mod_eq_of_lt (by omega)).symm
  simp only [ZMod.val_natCast]
  rw [← h1, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The numbering `Grp ≃ Fin 4220` of `Z_844 ⋊ Z_5`. -/
def equivG : Grp ≃ Fin 4220 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.val
  left_inv g := grpOf_enc g
  right_inv n := Fin.ext (enc_grpOf n.isLt)

end BipartiteDD.Haar.Meta844
