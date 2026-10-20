import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The group `AGL(1,7) × Z_21` of order 882 of the (8,5) record on 1764 vertices.

`AGL(1,7)` is the group of maps `t ↦ a t + b` on `ZMod 7` with `a ≠ 0`, with `(b₁,a₁)(b₂,a₂) = (a₁ b₂ + b₁, a₁ a₂)`.
Since `3` generates the units of `ZMod 7`, we write `a = 3 ^ y` with `y ∈ ZMod 6`, and an element is a triple
`(x, y, z)` with `x ∈ ZMod 7` (the translation `b`), `y ∈ ZMod 6` (the exponent of the multiplier) and
`z ∈ ZMod 21`. The product is
`(x, y, z) * (x', y', z') = (x + 3 ^ y * x', y + y', z + z')`
(the `Z_144 ⋊ Z_6` pattern of `Z144.lean`). The map `y ↦ 3 ^ y.val` is a homomorphism `ZMod 6 → ZMod 7`
because `3 ^ 6 = 1` in `ZMod 7`; `tw_add` checks this on all 36 pairs.
The numbering of the elements by `ℕ` is `n = 42 z + 7 y + x`. -/

namespace BipartiteDD.Haar.AGL17Z21

/-- The multiplier `3 ^ y` for `y : ZMod 6`. -/
def tw (y : ZMod 6) : ZMod 7 := 3 ^ y.val

theorem tw_zero : tw 0 = 1 := by decide

theorem tw_add : ∀ y z : ZMod 6, tw (y + z) = tw y * tw z := by decide

/-- Elements of `AGL(1,7) × Z_21`. -/
@[ext] structure Grp where
  x : ZMod 7
  y : ZMod 6
  z : ZMod 21
  deriving DecidableEq

instance : Group Grp where
  mul p q := ⟨p.x + tw p.y * q.x, p.y + q.y, p.z + q.z⟩
  one := ⟨0, 0, 0⟩
  inv p := ⟨-(tw (-p.y) * p.x), -p.y, -p.z⟩
  mul_assoc a b c := by
    ext
    · show a.x + tw a.y * b.x + tw (a.y + b.y) * c.x = a.x + tw a.y * (b.x + tw b.y * c.x)
      rw [tw_add]
      ring
    · show a.y + b.y + c.y = a.y + (b.y + c.y)
      exact add_assoc _ _ _
    · show a.z + b.z + c.z = a.z + (b.z + c.z)
      exact add_assoc _ _ _
  one_mul a := by
    ext
    · show 0 + tw 0 * a.x = a.x
      rw [tw_zero]
      ring
    · show 0 + a.y = a.y
      exact zero_add _
    · show 0 + a.z = a.z
      exact zero_add _
  mul_one a := by
    ext
    · show a.x + tw a.y * 0 = a.x
      ring
    · show a.y + 0 = a.y
      exact add_zero _
    · show a.z + 0 = a.z
      exact add_zero _
  inv_mul_cancel a := by
    ext
    · show -(tw (-a.y) * a.x) + tw (-a.y) * a.x = 0
      ring
    · show -a.y + a.y = 0
      exact neg_add_cancel _
    · show -a.z + a.z = 0
      exact neg_add_cancel _

/-- The triples `(x, y, z)`. -/
def equivProd : Grp ≃ ZMod 7 × ZMod 6 × ZMod 21 where
  toFun g := (g.x, g.y, g.z)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Grp := Fintype.ofEquiv (ZMod 7 × ZMod 6 × ZMod 21) equivProd.symm

theorem card_grp : Fintype.card Grp = 882 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod, ZMod.card, ZMod.card,
    ZMod.card]

/-- The element with index `n`, for `n < 882`: `x = n % 7`, `y = n / 7 % 6`, `z = n / 42`. -/
def grpOf (n : ℕ) : Grp :=
  ⟨((n % 7 : ℕ) : ZMod 7), ((n / 7 % 6 : ℕ) : ZMod 6), ((n / 42 : ℕ) : ZMod 21)⟩

/-- Every element has an index below 882. -/
theorem exists_grpOf (g : Grp) : ∃ n < 882, grpOf n = g := by
  have hx : g.x.val < 7 := ZMod.val_lt _
  have hy : g.y.val < 6 := ZMod.val_lt _
  have hz : g.z.val < 21 := ZMod.val_lt _
  have h1 : (42 * g.z.val + 7 * g.y.val + g.x.val) % 7 = g.x.val := by omega
  have h2 : (42 * g.z.val + 7 * g.y.val + g.x.val) / 7 % 6 = g.y.val := by omega
  have h3 : (42 * g.z.val + 7 * g.y.val + g.x.val) / 42 = g.z.val := by omega
  refine ⟨42 * g.z.val + 7 * g.y.val + g.x.val, by omega, ?_⟩
  simp only [grpOf, h1, h2, h3, ZMod.natCast_zmod_val]

end BipartiteDD.Haar.AGL17Z21
