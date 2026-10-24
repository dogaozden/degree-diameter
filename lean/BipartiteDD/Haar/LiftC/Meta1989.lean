import Mathlib.Algebra.Group.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_1989 ⋊ Z_24` of the (5,10) record on 95472 vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod 1989` and `y ∈ ZMod 24`, with product
`(x, y) * (x', y') = (x + 461 ^ y.val * x', y + y')`. This is the `meta 1989 24 461` group of
`research/lifts/sols/d5D10_n95472_haar_meta1989_24_461.txt`, whose rule is `(a,j)(b,l) = (a + r^j b, j + l)` with
`r = 461`. The map `y ↦ 461 ^ y.val` is a homomorphism `ZMod 24 → ZMod 1989` because `461 ^ 24 = 1` in `ZMod 1989`;
`tw_add` checks this on all 576 pairs.

The index of `(x, y)` is `x.val * 24 + y.val`, the index `a * 24 + j` of `research/lifts/coordinator_check/build.py`. -/

namespace BipartiteDD.Haar.LiftC.Meta1989

/-- The twist `461 ^ y` for `y : ZMod 24`. -/
def tw (y : ZMod 24) : ZMod 1989 := 461 ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod 24, tw (y + z) = tw y * tw z := by decide +kernel

/-- Elements of `Z_1989 ⋊ Z_24`. -/
@[ext] structure Grp where
  x : ZMod 1989
  y : ZMod 24
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

/-- The index of an element: `x.val * 24 + y.val`, in `[0, 47736)`. -/
def enc (g : Grp) : ℕ := g.x.val * 24 + g.y.val

/-- The element with index `n`: `(n / 24, n % 24)`. Inverse to `enc` on `n < 47736`. -/
def grpOf (n : ℕ) : Grp := ⟨(n / 24 : ℕ), (n % 24 : ℕ)⟩

theorem enc_lt (g : Grp) : enc g < 47736 := by
  have h1 := ZMod.val_lt g.x
  have h2 := ZMod.val_lt g.y
  unfold enc
  omega

theorem grpOf_enc (g : Grp) : grpOf (enc g) = g := by
  have h2 := ZMod.val_lt g.y
  have hd : (g.x.val * 24 + g.y.val) / 24 = g.x.val := by omega
  have hm : (g.x.val * 24 + g.y.val) % 24 = g.y.val := by omega
  unfold grpOf enc
  rw [hd, hm, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem enc_grpOf {n : ℕ} (hn : n < 47736) : enc (grpOf n) = n := by
  unfold enc grpOf
  have h1 : (n / 24 : ℕ) = (n / 24) % 1989 := (Nat.mod_eq_of_lt (by omega)).symm
  simp only [ZMod.val_natCast]
  rw [← h1, Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The numbering `Grp ≃ Fin 47736` of `Z_1989 ⋊ Z_24`. -/
def equivG : Grp ≃ Fin 47736 where
  toFun g := ⟨enc g, enc_lt g⟩
  invFun n := grpOf n.val
  left_inv g := grpOf_enc g
  right_inv n := Fin.ext (enc_grpOf n.isLt)

end BipartiteDD.Haar.LiftC.Meta1989
