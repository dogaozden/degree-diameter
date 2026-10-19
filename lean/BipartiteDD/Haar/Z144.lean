import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_144 ⋊ Z_6` of the (8,5) record on 1728 vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod 144` and `y ∈ ZMod 6`, with product
`(x, y) * (x', y') = (x + 25 ^ y.val * x', y + y')`. This is the product `mul` of
`research/d5/build_haar.py` (`pw[j] = 25 ^ j mod 144`). The map `y ↦ 25 ^ y.val` is a
homomorphism `ZMod 6 → ZMod 144` because `25 ^ 6 = 1` in `ZMod 144`; `tw_add` checks this
on all 36 pairs. -/

namespace BipartiteDD.Haar.Z144

/-- The twist `25 ^ y` for `y : ZMod 6`. -/
def tw (y : ZMod 6) : ZMod 144 := 25 ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod 6, tw (y + z) = tw y * tw z := by decide

/-- Elements of `Z_144 ⋊ Z_6`. -/
@[ext] structure Grp where
  x : ZMod 144
  y : ZMod 6
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

/-- The pairs `(x, y)`, as a type with `Fintype`. -/
def equivProd : Grp ≃ ZMod 144 × ZMod 6 where
  toFun g := (g.x, g.y)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Grp := Fintype.ofEquiv (ZMod 144 × ZMod 6) equivProd.symm

theorem card_grp : Fintype.card Grp = 864 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, ZMod.card, ZMod.card]

/-- The connection set `S` of the (8,5) record on 1728 vertices, in the order of its record file. -/
def s8 : Fin 8 → Grp :=
  ![⟨0, 0⟩, ⟨30, 5⟩, ⟨116, 3⟩, ⟨73, 1⟩, ⟨32, 4⟩, ⟨25, 0⟩, ⟨52, 2⟩, ⟨119, 2⟩]

/-- `S` as a finset. -/
def S8 : Finset Grp := Finset.univ.image s8

theorem card_S8 : S8.card = 8 := by decide +kernel

theorem s8_mem (i : Fin 8) : s8 i ∈ S8 :=
  Finset.mem_image_of_mem s8 (Finset.mem_univ i)

end BipartiteDD.Haar.Z144
