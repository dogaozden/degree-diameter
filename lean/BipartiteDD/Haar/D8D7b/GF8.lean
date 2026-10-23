import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic

/-! The field `GF(8) = GF(2)[x] / (x^3 + x + 1)`, as a commutative ring on `Fin 8`.

An element is a number `0 … 7`, whose bit `i` is the coefficient of `x^i`. The sum is `xor`. The product is the
product of polynomials, reduced by `x^3 = x + 1` and `x^4 = x^2 + x`; `mulN` computes it with bit operations,
which the kernel evaluates. The ring axioms are checked by `decide` on the 8, 64 or 512 cases. Since the
characteristic is 2, every element is its own negative.

`F8` is a `def`, not an `abbrev`, so that the ring structure here does not compete with the one of `Fin 8`. -/

namespace BipartiteDD.Haar.D8D7b

/-- `GF(8)`, with the ring structure of this file. -/
def F8 := Fin 8

instance : DecidableEq F8 := inferInstanceAs (DecidableEq (Fin 8))

instance : Fintype F8 := inferInstanceAs (Fintype (Fin 8))

/-- The product of the polynomials `a` and `b` (bits `0 … 2`) over `GF(2)`, reduced modulo `x^3 + x + 1`. -/
def mulN (a b : ℕ) : ℕ :=
  let m := (if b &&& 1 = 1 then a else 0) ^^^ (if b &&& 2 = 2 then a <<< 1 else 0) ^^^
    (if b &&& 4 = 4 then a <<< 2 else 0)
  let m := if m &&& 16 = 16 then m ^^^ 22 else m
  if m &&& 8 = 8 then m ^^^ 11 else m

/-- The element of `GF(8)` with number `k % 8`. -/
def ofN (k : ℕ) : F8 := (⟨k % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8)

/-- The number of an element of `GF(8)`, below 8. -/
def toN (x : F8) : ℕ := (x : Fin 8).val

/-- The sum: `xor`. -/
def addF (a b : F8) : F8 := ofN (toN a ^^^ toN b)

/-- The product, reduced modulo `x^3 + x + 1`. -/
def mulF (a b : F8) : F8 := ofN (mulN (toN a) (toN b))

/-- The zero element, `0`. -/
def zeroF : F8 := ofN 0

/-- The unit element, `1`. -/
def oneF : F8 := ofN 1

/-- Every element is its own negative. -/
def negF (a : F8) : F8 := a

theorem addF_assoc : ∀ a b c : F8, addF (addF a b) c = addF a (addF b c) := by decide +kernel

theorem zero_addF : ∀ a : F8, addF zeroF a = a := by decide +kernel

theorem addF_zero : ∀ a : F8, addF a zeroF = a := by decide +kernel

theorem addF_comm : ∀ a b : F8, addF a b = addF b a := by decide +kernel

theorem addF_self : ∀ a : F8, addF a a = zeroF := by decide +kernel

theorem mulF_assoc : ∀ a b c : F8, mulF (mulF a b) c = mulF a (mulF b c) := by decide +kernel

theorem one_mulF : ∀ a : F8, mulF oneF a = a := by decide +kernel

theorem mulF_one : ∀ a : F8, mulF a oneF = a := by decide +kernel

theorem mulF_comm : ∀ a b : F8, mulF a b = mulF b a := by decide +kernel

theorem left_distribF : ∀ a b c : F8, mulF a (addF b c) = addF (mulF a b) (mulF a c) := by decide +kernel

theorem right_distribF : ∀ a b c : F8, mulF (addF a b) c = addF (mulF a c) (mulF b c) := by decide +kernel

theorem zero_mulF : ∀ a : F8, mulF zeroF a = zeroF := by decide +kernel

theorem mul_zeroF : ∀ a : F8, mulF a zeroF = zeroF := by decide +kernel

instance : Zero F8 := ⟨zeroF⟩

instance : One F8 := ⟨oneF⟩

instance : Add F8 := ⟨addF⟩

instance : Mul F8 := ⟨mulF⟩

instance : Neg F8 := ⟨negF⟩

instance : CommRing F8 where
  add_assoc := addF_assoc
  zero_add := zero_addF
  add_zero := addF_zero
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  neg_add_cancel := addF_self
  add_comm := addF_comm
  mul_assoc := mulF_assoc
  one_mul := one_mulF
  mul_one := mulF_one
  npow := npowRec
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
  left_distrib := left_distribF
  right_distrib := right_distribF
  zero_mul := zero_mulF
  mul_zero := mul_zeroF
  mul_comm := mulF_comm
  zsmul := zsmulRec
  natCast := Nat.unaryCast
  natCast_zero := rfl
  natCast_succ := fun _ => rfl
  intCast := fun z => Nat.unaryCast z.natAbs
  intCast_ofNat := fun _ => rfl
  intCast_negSucc := fun _ => rfl

end BipartiteDD.Haar.D8D7b
