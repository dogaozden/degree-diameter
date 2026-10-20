import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-! The Heisenberg group mod 11, of order 1331, of the (9,5) record on 2662 vertices.

An element `(a, b, c)` is the matrix `[[1, a, c], [0, 1, b], [0, 0, 1]]` over `ZMod 11`, and the product is
`(a, b, c) * (a', b', c') = (a + a', b + b', c + c' + a * b')`. The numbering of the elements by `ℕ` is
`n = 121 a + 11 b + c`. -/

namespace BipartiteDD.Haar.Heis11

/-- Elements of the Heisenberg group mod 11. -/
@[ext] structure Grp where
  a : ZMod 11
  b : ZMod 11
  c : ZMod 11
  deriving DecidableEq

instance : Group Grp where
  mul p q := ⟨p.a + q.a, p.b + q.b, p.c + q.c + p.a * q.b⟩
  one := ⟨0, 0, 0⟩
  inv p := ⟨-p.a, -p.b, -p.c + p.a * p.b⟩
  mul_assoc x y z := by
    ext
    · show x.a + y.a + z.a = x.a + (y.a + z.a)
      ring
    · show x.b + y.b + z.b = x.b + (y.b + z.b)
      ring
    · show x.c + y.c + x.a * y.b + z.c + (x.a + y.a) * z.b =
        x.c + (y.c + z.c + y.a * z.b) + x.a * (y.b + z.b)
      ring
  one_mul x := by
    ext
    · show 0 + x.a = x.a
      ring
    · show 0 + x.b = x.b
      ring
    · show 0 + x.c + 0 * x.b = x.c
      ring
  mul_one x := by
    ext
    · show x.a + 0 = x.a
      ring
    · show x.b + 0 = x.b
      ring
    · show x.c + 0 + x.a * 0 = x.c
      ring
  inv_mul_cancel x := by
    ext
    · show -x.a + x.a = 0
      ring
    · show -x.b + x.b = 0
      ring
    · show -x.c + x.a * x.b + x.c + -x.a * x.b = 0
      ring

/-- The triples `(a, b, c)`. -/
def equivProd : Grp ≃ ZMod 11 × ZMod 11 × ZMod 11 where
  toFun g := (g.a, g.b, g.c)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype Grp := Fintype.ofEquiv (ZMod 11 × ZMod 11 × ZMod 11) equivProd.symm

theorem card_grp : Fintype.card Grp = 1331 := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, Fintype.card_prod, ZMod.card]

/-- The element with index `n`, for `n < 1331`: `a = n / 121`, `b = n / 11 % 11`, `c = n % 11`. -/
def grpOf (n : ℕ) : Grp :=
  ⟨((n / 121 : ℕ) : ZMod 11), ((n / 11 % 11 : ℕ) : ZMod 11), ((n % 11 : ℕ) : ZMod 11)⟩

/-- Every element has an index below 1331. -/
theorem exists_grpOf (g : Grp) : ∃ n < 1331, grpOf n = g := by
  have ha : g.a.val < 11 := ZMod.val_lt _
  have hb : g.b.val < 11 := ZMod.val_lt _
  have hc : g.c.val < 11 := ZMod.val_lt _
  have h1 : (121 * g.a.val + 11 * g.b.val + g.c.val) / 121 = g.a.val := by omega
  have h2 : (121 * g.a.val + 11 * g.b.val + g.c.val) / 11 % 11 = g.b.val := by omega
  have h3 : (121 * g.a.val + 11 * g.b.val + g.c.val) % 11 = g.c.val := by omega
  refine ⟨121 * g.a.val + 11 * g.b.val + g.c.val, by omega, ?_⟩
  simp only [grpOf, h1, h2, h3, ZMod.natCast_zmod_val]

end BipartiteDD.Haar.Heis11
