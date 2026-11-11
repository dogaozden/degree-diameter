import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Data.Fintype.Prod

/-! # The field with 25 elements, concretely

`GF25` is `Fin 25`; the element `c₀ + 5 c₁` is `c₀ + c₁ x` in `F₅[x]/(x² + 2)` (so `x² = 3`), the encoding of the
sol files (`research/frontier/build_haar2.py`: "field elements written as sum c_i p^i"). The ring axioms are checked
by `decide`. For the packed checks an element is written as `c₀ + 128 c₁` (`sp`): an integer product of two such
codes holds the coefficients of `1, x, x²` in separate 7-bit groups, and `red1` reduces a sum of two products back
(`c₀ + 3 c₂` and `c₁`, each mod 5, by a multiply-high division). The order of `SL(2,25)` comes from Mathlib's order of
`GL(2,25)` (`card_SL_two`). -/

namespace BipartiteDD.LeanAll

/-- The field with 25 elements. -/
def GF25 : Type := Fin 25

namespace GF25

instance : DecidableEq GF25 := inferInstanceAs (DecidableEq (Fin 25))

instance : Fintype GF25 := inferInstanceAs (Fintype (Fin 25))

instance : Inhabited GF25 := ⟨(0 : Fin 25)⟩

/-- The element with code `n % 25`. -/
def mk (n : ℕ) : GF25 := (⟨n % 25, Nat.mod_lt _ (by norm_num)⟩ : Fin 25)

/-- The code of an element. -/
def code (x : GF25) : ℕ := (x : Fin 25).val

theorem code_lt (x : GF25) : code x < 25 := (x : Fin 25).isLt

theorem code_mk {n : ℕ} (h : n < 25) : code (mk n) = n := Nat.mod_eq_of_lt h

theorem mk_code (x : GF25) : mk (code x) = x := Fin.ext (Nat.mod_eq_of_lt (code_lt x))

theorem code_inj {x y : GF25} (h : code x = code y) : x = y := Fin.ext h

/-- The coefficient of `1`. -/
def lo (x : GF25) : ℕ := code x % 5

/-- The coefficient of `x`. -/
def hi (x : GF25) : ℕ := code x / 5

theorem lo_lt (x : GF25) : lo x < 5 := Nat.mod_lt _ (by norm_num)

theorem hi_lt (x : GF25) : hi x < 5 := by have := code_lt x; unfold hi; omega

instance : Add GF25 := ⟨fun x y => mk ((lo x + lo y) % 5 + 5 * ((hi x + hi y) % 5))⟩
instance : Mul GF25 :=
  ⟨fun x y => mk ((lo x * lo y + 3 * (hi x * hi y)) % 5 + 5 * ((lo x * hi y + hi x * lo y) % 5))⟩
instance : Neg GF25 := ⟨fun x => mk ((5 - lo x) % 5 + 5 * ((5 - hi x) % 5))⟩
instance : Zero GF25 := ⟨mk 0⟩
instance : One GF25 := ⟨mk 1⟩

instance : CommRing GF25 where
  add_assoc := by decide +kernel
  zero_add := by decide +kernel
  add_zero := by decide +kernel
  add_comm := by decide +kernel
  neg_add_cancel := by decide +kernel
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  zero_mul := by decide +kernel
  mul_zero := by decide +kernel
  left_distrib := by decide +kernel
  right_distrib := by decide +kernel
  mul_comm := by decide +kernel
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : NoZeroDivisors GF25 where
  eq_zero_or_eq_zero_of_mul_eq_zero := by
    have : ∀ a b : GF25, a * b = 0 → a = 0 ∨ b = 0 := by decide +kernel
    exact fun {a b} h => this a b h

instance : Nontrivial GF25 := ⟨⟨0, 1, by decide⟩⟩

theorem lo_add : ∀ x y : GF25, lo (x + y) = (lo x + lo y) % 5 := by decide +kernel
theorem hi_add : ∀ x y : GF25, hi (x + y) = (hi x + hi y) % 5 := by decide +kernel
theorem lo_mul : ∀ x y : GF25, lo (x * y) = (lo x * lo y + 3 * (hi x * hi y)) % 5 := by decide +kernel
theorem hi_mul : ∀ x y : GF25, hi (x * y) = (lo x * hi y + hi x * lo y) % 5 := by decide +kernel

/-! ## Spaced codes -/

/-- `c₀ + 128 c₁`. -/
def sp (x : GF25) : ℕ := lo x + 128 * hi x

theorem sp_lt (x : GF25) : sp x < 517 := by have := lo_lt x; have := hi_lt x; unfold sp; omega

theorem sp_inj : ∀ {x y : GF25}, sp x = sp y → x = y := by
  have : ∀ x y : GF25, sp x = sp y → x = y := by decide +kernel
  exact fun {x y} h => this x y h

theorem sp_zero : sp 0 = 0 := by decide

theorem sp_one : sp 1 = 1 := by decide

/-- `u / 5` for `u < 1024`, as a multiply-high step. -/
def q5 (u : ℕ) : ℕ := ((u * 205) >>> 10) &&& 1023

theorem q5_eq : ∀ u, u < 1024 → q5 u = u / 5 := by decide +kernel

/-- Reduction of a sum of two products of spaced codes. -/
def red1 (v : ℕ) : ℕ :=
  ((v &&& 127) + 3 * ((v >>> 14) &&& 127) - 5 * q5 ((v &&& 127) + 3 * ((v >>> 14) &&& 127))) +
    128 * (((v >>> 7) &&& 127) - 5 * q5 ((v >>> 7) &&& 127))

theorem red1_eq {c0 c1 c2 : ℕ} (h0 : c0 < 128) (h1 : c1 < 128) (h2 : c2 < 128) :
    red1 (c0 + 128 * c1 + 16384 * c2) = (c0 + 3 * c2) % 5 + 128 * (c1 % 5) := by
  have m127 : (127 : ℕ) = 2 ^ 7 - 1 := rfl
  have e0 : (c0 + 128 * c1 + 16384 * c2) &&& 127 = c0 := by
    rw [m127, Nat.and_two_pow_sub_one_eq_mod]; omega
  have e1 : ((c0 + 128 * c1 + 16384 * c2) >>> 7) &&& 127 = c1 := by
    rw [m127, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]; omega
  have e2 : ((c0 + 128 * c1 + 16384 * c2) >>> 14) &&& 127 = c2 := by
    rw [m127, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]; omega
  unfold red1
  rw [e0, e1, e2, q5_eq _ (by omega), q5_eq _ (by omega)]
  omega

theorem sp_lin (a b e g : GF25) : sp a * sp e + sp b * sp g =
    (lo a * lo e + lo b * lo g) + 128 * (lo a * hi e + hi a * lo e + (lo b * hi g + hi b * lo g)) +
      16384 * (hi a * hi e + hi b * hi g) := by
  unfold sp; ring

/-- **The field-level step.** -/
theorem red1_sp (a b e g : GF25) : red1 (sp a * sp e + sp b * sp g) = sp (a * e + b * g) := by
  have la := lo_lt a; have lb := lo_lt b; have le := lo_lt e; have lg := lo_lt g
  have ha := hi_lt a; have hb := hi_lt b; have he := hi_lt e; have hg := hi_lt g
  have p1 : lo a * lo e ≤ 16 := by nlinarith
  have p2 : lo b * lo g ≤ 16 := by nlinarith
  have p3 : lo a * hi e ≤ 16 := by nlinarith
  have p4 : hi a * lo e ≤ 16 := by nlinarith
  have p5 : lo b * hi g ≤ 16 := by nlinarith
  have p6 : hi b * lo g ≤ 16 := by nlinarith
  have p7 : hi a * hi e ≤ 16 := by nlinarith
  have p8 : hi b * hi g ≤ 16 := by nlinarith
  rw [sp_lin, red1_eq (by omega) (by omega) (by omega)]
  unfold sp
  rw [lo_add, hi_add, lo_mul, lo_mul, hi_mul, hi_mul]
  generalize lo a * lo e = A1 at *
  generalize lo b * lo g = A2 at *
  generalize lo a * hi e = A3 at *
  generalize hi a * lo e = A4 at *
  generalize lo b * hi g = A5 at *
  generalize hi b * lo g = A6 at *
  generalize hi a * hi e = A7 at *
  generalize hi b * hi g = A8 at *
  omega

theorem lin_lt (a b e g : GF25) : sp a * sp e + sp b * sp g < 2 ^ 20 := by
  have h1 := sp_lt a; have h2 := sp_lt b; have h3 := sp_lt e; have h4 := sp_lt g
  have : sp a * sp e + sp b * sp g ≤ 516 * 516 + 516 * 516 := by
    apply Nat.add_le_add <;> apply Nat.mul_le_mul <;> omega
  have : (2 : ℕ) ^ 20 = 1048576 := by norm_num
  omega

/-! ## The order of `SL(2, GF25)` -/

open Matrix

/-- `|SL(2,F)| (q - 1) = |GL(2,F)|` for a finite field with `q` elements. -/
theorem card_SL_two (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) * (Fintype.card F - 1) =
      (Fintype.card F ^ 2 - 1) * (Fintype.card F ^ 2 - Fintype.card F) := by
  have h1 := Matrix.card_GL_field (𝔽 := F) 2
  rw [Fin.prod_univ_two] at h1
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one] at h1
  have h2 : Nat.card (SpecialLinearGroup (Fin 2) F) =
      Nat.card (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker := by
    rw [← SpecialLinearGroup.range_toGL_eq_ker_det]
    exact Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv
  have h3 := Subgroup.card_mul_index (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker
  have h4 : (GeneralLinearGroup.det : GL (Fin 2) F →* Fˣ).ker.index = Fintype.card F - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr GeneralLinearGroup.det_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units]
  rw [h2, ← h4, h3, h1]

instance : IsDomain GF25 := NoZeroDivisors.to_isDomain GF25

theorem card_GF25 : Fintype.card GF25 = 25 := Fintype.card_fin 25

theorem card_SL25 : Fintype.card (SpecialLinearGroup (Fin 2) GF25) = 15600 := by
  let _ : Field GF25 := Fintype.fieldOfDomain GF25
  have h := card_SL_two GF25
  rw [card_GF25, Nat.card_eq_fintype_card] at h
  norm_num at h
  omega

end GF25

end BipartiteDD.LeanAll
