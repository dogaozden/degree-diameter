import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic

/-! # The field with 9 elements, concretely

`GF9` is `Fin 9` read as `a₀ + a₁ x` over `F₃` with code `a₀ + 3a₁`, and multiplication modulo `x² + 1` (the
field of research/d13D7/hexgen2.c for `q = 9`: `α² = 2`). The ring axioms are checked by `decide`. -/

namespace BipartiteDD.LeanAll

/-- The field with 9 elements. -/
def GF9 : Type := Fin 9

namespace GF9

instance : DecidableEq GF9 := inferInstanceAs (DecidableEq (Fin 9))

instance : Fintype GF9 := inferInstanceAs (Fintype (Fin 9))

instance : Inhabited GF9 := ⟨(0 : Fin 9)⟩

/-- The element with code `n % 9`. -/
def mk (n : ℕ) : GF9 := (⟨n % 9, Nat.mod_lt _ (by decide)⟩ : Fin 9)

/-- The code of an element. -/
def code (x : GF9) : ℕ := (x : Fin 9).val

theorem code_lt (x : GF9) : code x < 9 := (x : Fin 9).isLt

theorem code_mk {n : ℕ} (h : n < 9) : code (mk n) = n := Nat.mod_eq_of_lt h

theorem mk_code (x : GF9) : mk (code x) = x := Fin.ext (Nat.mod_eq_of_lt (code_lt x))

theorem code_inj {x y : GF9} (h : code x = code y) : x = y := Fin.ext h

/-- The sum of codes. -/
def addC (a b : ℕ) : ℕ := (a % 3 + b % 3) % 3 + 3 * ((a / 3 + b / 3) % 3)

/-- The negative of a code. -/
def negC (a : ℕ) : ℕ := (3 - a % 3) % 3 + 3 * ((3 - a / 3) % 3)

/-- The product of codes, modulo `x² + 1`. -/
def mulC (a b : ℕ) : ℕ :=
  (a % 3 * (b % 3) + 2 * (a / 3 * (b / 3))) % 3 + 3 * ((a % 3 * (b / 3) + a / 3 * (b % 3)) % 3)

instance : Add GF9 := ⟨fun x y => mk (addC (code x) (code y))⟩
instance : Mul GF9 := ⟨fun x y => mk (mulC (code x) (code y))⟩
instance : Neg GF9 := ⟨fun x => mk (negC (code x))⟩
instance : Zero GF9 := ⟨mk 0⟩
instance : One GF9 := ⟨mk 1⟩

theorem add_def (x y : GF9) : x + y = mk (addC (code x) (code y)) := rfl
theorem mul_def (x y : GF9) : x * y = mk (mulC (code x) (code y)) := rfl

instance : CommRing GF9 where
  add_assoc := by decide
  zero_add := by decide
  add_zero := by decide
  add_comm := by decide
  neg_add_cancel := by decide
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  zero_mul := by decide
  mul_zero := by decide
  left_distrib := by decide
  right_distrib := by decide
  mul_comm := by decide
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : NoZeroDivisors GF9 where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    have : ∀ a b : GF9, a * b = 0 → a = 0 ∨ b = 0 := by decide
    exact fun {a b} h => this a b h

end GF9

end BipartiteDD.LeanAll
