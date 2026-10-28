import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fintype.Prod

/-! # The field with 8 elements, concretely

`GF8` is `Fin 8` read as polynomials of degree `< 3` over `F₂` (bit `i` is the coefficient of `xⁱ`), with
multiplication modulo `x³ + x + 1`. The ring axioms are checked by `decide`. For the packed checks an element is
also written with its bits spaced three apart (`sp`), so that integer products of spaced numbers carry no bits
between coefficients; `red1` reduces such a product back (parity of each coefficient, then `x³ = x + 1`,
`x⁴ = x² + x`). -/

namespace BipartiteDD.LeanAll

/-- The field with 8 elements. -/
def GF8 : Type := Fin 8

namespace GF8

instance : DecidableEq GF8 := inferInstanceAs (DecidableEq (Fin 8))

instance : Fintype GF8 := inferInstanceAs (Fintype (Fin 8))

instance : Inhabited GF8 := ⟨(0 : Fin 8)⟩

/-- The element with bits `n % 8`. -/
def mk (n : ℕ) : GF8 := (⟨n % 8, Nat.mod_lt _ (by norm_num)⟩ : Fin 8)

/-- The bits of an element. -/
def code (x : GF8) : ℕ := (x : Fin 8).val

theorem code_lt (x : GF8) : code x < 8 := (x : Fin 8).isLt

theorem code_mk {n : ℕ} (h : n < 8) : code (mk n) = n := Nat.mod_eq_of_lt h

theorem mk_code (x : GF8) : mk (code x) = x := Fin.ext (Nat.mod_eq_of_lt (code_lt x))

theorem code_inj {x y : GF8} (h : code x = code y) : x = y := Fin.ext h

/-- Bit `i` of `n`. -/
def bit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The product modulo `x³ + x + 1`. -/
def mulC (a b : ℕ) : ℕ :=
  let c0 := bit a 0 * bit b 0
  let c1 := bit a 0 * bit b 1 + bit a 1 * bit b 0
  let c2 := bit a 0 * bit b 2 + bit a 1 * bit b 1 + bit a 2 * bit b 0
  let c3 := bit a 1 * bit b 2 + bit a 2 * bit b 1
  let c4 := bit a 2 * bit b 2
  (c0 + c3) % 2 + 2 * ((c1 + c3 + c4) % 2) + 4 * ((c2 + c4) % 2)

instance : Add GF8 := ⟨fun x y => mk (code x ^^^ code y)⟩
instance : Mul GF8 := ⟨fun x y => mk (mulC (code x) (code y))⟩
instance : Neg GF8 := ⟨fun x => x⟩
instance : Zero GF8 := ⟨mk 0⟩
instance : One GF8 := ⟨mk 1⟩

theorem add_def (x y : GF8) : x + y = mk (code x ^^^ code y) := rfl
theorem mul_def (x y : GF8) : x * y = mk (mulC (code x) (code y)) := rfl

instance : CommRing GF8 where
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

instance : NoZeroDivisors GF8 where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    have : ∀ a b : GF8, a * b = 0 → a = 0 ∨ b = 0 := by decide
    exact fun {a b} h => this a b h

/-! ## Spaced codes -/

/-- The bits of `x` at positions `0, 3, 6`. -/
def sp (x : GF8) : ℕ := bit (code x) 0 + 8 * bit (code x) 1 + 64 * bit (code x) 2

/-- Back from a spaced code. -/
def unsp (v : ℕ) : GF8 := mk (bit v 0 + 2 * bit v 3 + 4 * bit v 6)

/-- Reduction of a sum of two products of spaced codes (each field below `2 ^ 15`). -/
def red1 (v : ℕ) : ℕ := ((v &&& 73) + ((v >>> 9) &&& 1) * 9 + ((v >>> 12) &&& 1) * 72) &&& 73

theorem sp_lt (x : GF8) : sp x < 74 := by revert x; decide

theorem unsp_sp (x : GF8) : unsp (sp x) = x := by revert x; decide

theorem sp_inj {x y : GF8} (h : sp x = sp y) : x = y := by rw [← unsp_sp x, h, unsp_sp]

theorem sp_zero : sp 0 = 0 := by decide

theorem sp_one : sp 1 = 1 := by decide

/-- **The field-level step.** -/
theorem red1_sp : ∀ a b e g : GF8, red1 (sp a * sp e + sp b * sp g) = sp (a * e + b * g) := by decide

theorem lin_lt (a b e g : GF8) : sp a * sp e + sp b * sp g < 2 ^ 15 := by
  have h1 := sp_lt a; have h2 := sp_lt b; have h3 := sp_lt e; have h4 := sp_lt g
  have : sp a * sp e + sp b * sp g ≤ 73 * 73 + 73 * 73 := by
    apply Nat.add_le_add <;> apply Nat.mul_le_mul <;> omega
  omega

/-! ## The order of `SL(2, GF8)` -/

open Matrix

/-- `SL(2, R)` as quadruples with `a d - b c = 1`. -/
def slEquiv (R : Type*) [CommRing R] :
    SpecialLinearGroup (Fin 2) R ≃ {v : R × R × R × R // v.1 * v.2.2.2 - v.2.1 * v.2.2.1 = 1} where
  toFun A := ⟨(A 0 0, A 0 1, A 1 0, A 1 1), by
    have h := A.2
    rw [det_fin_two] at h
    exact h⟩
  invFun v := ⟨!![v.1.1, v.1.2.1; v.1.2.2.1, v.1.2.2.2], by rw [det_fin_two_of]; exact v.2⟩
  left_inv A := by
    apply SpecialLinearGroup.ext
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  right_inv v := rfl

theorem card_SL8 : Fintype.card (SpecialLinearGroup (Fin 2) GF8) = 504 := by
  rw [Fintype.card_congr (slEquiv GF8), Fintype.card_subtype]
  decide +kernel

end GF8

end BipartiteDD.LeanAll
