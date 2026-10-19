import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `Z_131 ⋊ Z_10` of the (9,5) record on 2620 vertices.

Elements are pairs `(x, y)` with `x ∈ ZMod 131` and `y ∈ ZMod 10`, with product
`(x, y) * (x', y') = (x + 53 ^ y.val * x', y + y')`. This is the product `mul` of
`research/d5/build_haar.py` (`pw[j] = 53 ^ j mod 131`). The map `y ↦ 53 ^ y.val` is a homomorphism
`ZMod 10 → ZMod 131` because `53 ^ 10 = 1` in `ZMod 131`; `tw_add` checks this on all 100 pairs. -/

namespace BipartiteDD.Haar.Z131

/-- The twist `53 ^ y` for `y : ZMod 10`. -/
def tw (y : ZMod 10) : ZMod 131 := 53 ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod 10, tw (y + z) = tw y * tw z := by decide

/-- Elements of `Z_131 ⋊ Z_10`. -/
@[ext] structure Grp where
  x : ZMod 131
  y : ZMod 10
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
def equivProd : Grp ≃ ZMod 131 × ZMod 10 where
  toFun g := (g.x, g.y)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Grp := Fintype.ofEquiv (ZMod 131 × ZMod 10) equivProd.symm

theorem card_grp : Fintype.card Grp = 1310 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, ZMod.card, ZMod.card]

/-- The connection set `S` of the record: the first element `(0, 0)` and the eight others of
`research/d5/sols/h2_d9_N1310_m131_k10_l53.txt`, in file order. -/
def s9 : Fin 9 → Grp :=
  ![⟨0, 0⟩, ⟨74, 3⟩, ⟨9, 2⟩, ⟨103, 4⟩, ⟨89, 9⟩, ⟨105, 4⟩, ⟨36, 1⟩, ⟨54, 5⟩, ⟨111, 3⟩]

/-- `S` as a finset. -/
def S9 : Finset Grp := Finset.univ.image s9

theorem card_S9 : S9.card = 9 := by decide +kernel

theorem s9_mem (i : Fin 9) : s9 i ∈ S9 :=
  Finset.mem_image_of_mem s9 (Finset.mem_univ i)

end BipartiteDD.Haar.Z131
