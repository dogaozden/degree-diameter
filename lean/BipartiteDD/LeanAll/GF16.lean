import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.Fintype.Prod

/-! # The field with 16 elements, concretely

`GF16` is `Fin 16` read as polynomials of degree `< 4` over `F₂` (bit `i` is the coefficient of `xⁱ`), with
multiplication modulo `x⁴ + x + 1`. The ring axioms are checked by `decide`. For the packed checks an element is
also written with its bits spaced four apart (`sp`), so that integer products of spaced numbers carry no bits
between coefficients; `red1` reduces such a sum of products back (parity of each coefficient, then `x⁴ = x + 1`,
`x⁵ = x² + x`, `x⁶ = x³ + x²`). Same plan as `GF16.lean`. -/

namespace BipartiteDD.LeanAll

/-- The field with 8 elements. -/
def GF16 : Type := Fin 16

namespace GF16

instance : DecidableEq GF16 := inferInstanceAs (DecidableEq (Fin 16))

instance : Fintype GF16 := inferInstanceAs (Fintype (Fin 16))

instance : Inhabited GF16 := ⟨(0 : Fin 16)⟩

/-- The element with bits `n % 16`. -/
def mk (n : ℕ) : GF16 := (⟨n % 16, Nat.mod_lt _ (by norm_num)⟩ : Fin 16)

/-- The bits of an element. -/
def code (x : GF16) : ℕ := (x : Fin 16).val

theorem code_lt (x : GF16) : code x < 16 := (x : Fin 16).isLt

theorem code_mk {n : ℕ} (h : n < 16) : code (mk n) = n := Nat.mod_eq_of_lt h

theorem mk_code (x : GF16) : mk (code x) = x := Fin.ext (Nat.mod_eq_of_lt (code_lt x))

theorem code_inj {x y : GF16} (h : code x = code y) : x = y := Fin.ext h

/-- Bit `i` of `n`. -/
def bit (n i : ℕ) : ℕ := n / 2 ^ i % 2

/-- The product modulo `x⁴ + x + 1`. -/
def mulC (a b : ℕ) : ℕ :=
  let c0 := bit a 0 * bit b 0
  let c1 := bit a 0 * bit b 1 + bit a 1 * bit b 0
  let c2 := bit a 0 * bit b 2 + bit a 1 * bit b 1 + bit a 2 * bit b 0
  let c3 := bit a 0 * bit b 3 + bit a 1 * bit b 2 + bit a 2 * bit b 1 + bit a 3 * bit b 0
  let c4 := bit a 1 * bit b 3 + bit a 2 * bit b 2 + bit a 3 * bit b 1
  let c5 := bit a 2 * bit b 3 + bit a 3 * bit b 2
  let c6 := bit a 3 * bit b 3
  (c0 + c4) % 2 + 2 * ((c1 + c4 + c5) % 2) + 4 * ((c2 + c5 + c6) % 2) + 8 * ((c3 + c6) % 2)

instance : Add GF16 := ⟨fun x y => mk (code x ^^^ code y)⟩
instance : Mul GF16 := ⟨fun x y => mk (mulC (code x) (code y))⟩
instance : Neg GF16 := ⟨fun x => x⟩
instance : Zero GF16 := ⟨mk 0⟩
instance : One GF16 := ⟨mk 1⟩

theorem add_def (x y : GF16) : x + y = mk (code x ^^^ code y) := rfl
theorem mul_def (x y : GF16) : x * y = mk (mulC (code x) (code y)) := rfl

instance : CommRing GF16 where
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

instance : NoZeroDivisors GF16 where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    have : ∀ a b : GF16, a * b = 0 → a = 0 ∨ b = 0 := by decide
    exact fun {a b} h => this a b h

/-! ## Spaced codes -/

/-- The bits of `x` at positions `0, 4, 8, 12`. -/
def sp (x : GF16) : ℕ := bit (code x) 0 + 16 * bit (code x) 1 + 256 * bit (code x) 2 + 4096 * bit (code x) 3

/-- Back from a spaced code. -/
def unsp (v : ℕ) : GF16 := mk (bit v 0 + 2 * bit v 4 + 4 * bit v 8 + 8 * bit v 12)

/-- Reduction of a sum of two products of spaced codes (each field below `2 ^ 28`). -/
def red1 (v : ℕ) : ℕ :=
  ((v &&& 4369) + ((v >>> 16) &&& 1) * 17 + ((v >>> 20) &&& 1) * 272 + ((v >>> 24) &&& 1) * 4352) &&& 4369

theorem sp_lt (x : GF16) : sp x < 4370 := by revert x; decide

theorem unsp_sp (x : GF16) : unsp (sp x) = x := by revert x; decide

theorem sp_inj {x y : GF16} (h : sp x = sp y) : x = y := by rw [← unsp_sp x, h, unsp_sp]

theorem sp_zero : sp 0 = 0 := by decide

theorem sp_one : sp 1 = 1 := by decide

/-- **The field-level step** (all `16 ^ 4` cases). -/
theorem red1_sp : ∀ a b e g : GF16, red1 (sp a * sp e + sp b * sp g) = sp (a * e + b * g) := by decide +kernel

theorem lin_lt (a b e g : GF16) : sp a * sp e + sp b * sp g < 2 ^ 28 := by
  have h1 := sp_lt a; have h2 := sp_lt b; have h3 := sp_lt e; have h4 := sp_lt g
  have : sp a * sp e + sp b * sp g ≤ 4369 * 4369 + 4369 * 4369 := by
    apply Nat.add_le_add <;> apply Nat.mul_le_mul <;> omega
  omega

/-! ## The order of `SL(2, GF16)` -/

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

theorem card_SL16 : Fintype.card (SpecialLinearGroup (Fin 2) GF16) = 4080 := by
  rw [Fintype.card_congr (slEquiv GF16), Fintype.card_subtype]
  decide +kernel

end GF16

end BipartiteDD.LeanAll
