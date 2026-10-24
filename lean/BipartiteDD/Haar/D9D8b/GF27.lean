import Mathlib.Algebra.Ring.Defs

/-! The field `GF(27) = GF(3)[x] / (x³ + 2x + 1)` with a computable model on `Fin 27`.

The number `c₀ + 3 c₁ + 9 c₂` (`cᵢ ∈ {0, 1, 2}`) stands for `c₀ + c₁ x + c₂ x²`. The product reduces by
`x³ = x + 2`, which is `x³ + 2x + 1 = 0` over `GF(3)`. All operations are on `ℕ`, digit by digit, so the
ring laws are checked by kernel computation over the 27 values (`decide +kernel`). -/

namespace BipartiteDD.Haar.D9D8b

/-- The field `GF(27)`, as `Fin 27`. -/
def F27 : Type := Fin 27

instance : DecidableEq F27 := inferInstanceAs (DecidableEq (Fin 27))

/-- The number of the element, in `0 … 26`. -/
def F27.val (x : F27) : ℕ := Fin.val x

theorem F27.val_lt (x : F27) : x.val < 27 := Fin.isLt x

/-- The element with number `k`, for any `k` (reduced mod 27). -/
def ofN (k : ℕ) : F27 := (⟨k % 27, Nat.mod_lt _ (by decide)⟩ : Fin 27)

theorem ofN_val (x : F27) : ofN x.val = x := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (F27.val_lt x)

/-- Reduction of a polynomial with coefficients `c₀ … c₄` of `x⁰ … x⁴`: `x³ = x + 2`, `x⁴ = x² + 2x`. -/
def redN (c0 c1 c2 c3 c4 : ℕ) : ℕ :=
  (c0 + 2 * c3) % 3 + 3 * ((c1 + c3 + 2 * c4) % 3) + 9 * ((c2 + c4) % 3)

theorem redN_lt (c0 c1 c2 c3 c4 : ℕ) : redN c0 c1 c2 c3 c4 < 27 := by
  unfold redN
  omega

/-- Sum, digit by digit. -/
def addN (a b : ℕ) : ℕ :=
  (a % 3 + b % 3) % 3 + 3 * ((a / 3 % 3 + b / 3 % 3) % 3) + 9 * ((a / 9 + b / 9) % 3)

theorem addN_lt (a b : ℕ) : addN a b < 27 := by
  unfold addN
  omega

/-- Product of the polynomials of `a` and `b`, reduced. -/
def mulN (a b : ℕ) : ℕ :=
  redN (a % 3 * (b % 3)) (a % 3 * (b / 3 % 3) + a / 3 % 3 * (b % 3))
    (a % 3 * (b / 9) + a / 3 % 3 * (b / 3 % 3) + a / 9 * (b % 3))
    (a / 3 % 3 * (b / 9) + a / 9 * (b / 3 % 3)) (a / 9 * (b / 9))

theorem mulN_lt (a b : ℕ) : mulN a b < 27 :=
  redN_lt _ _ _ _ _

/-- Negation, digit by digit. -/
def negN (a : ℕ) : ℕ :=
  (3 - a % 3) % 3 + 3 * ((3 - a / 3 % 3) % 3) + 9 * ((3 - a / 9) % 3)

theorem negN_lt (a : ℕ) : negN a < 27 := by
  unfold negN
  omega

/-- The operations on `Fin 27`. -/
def addF (a b : Fin 27) : Fin 27 := ⟨addN a.val b.val, addN_lt _ _⟩
def mulF (a b : Fin 27) : Fin 27 := ⟨mulN a.val b.val, mulN_lt _ _⟩
def negF (a : Fin 27) : Fin 27 := ⟨negN a.val, negN_lt _⟩
def zeroF : Fin 27 := ⟨0, by decide⟩
def oneF : Fin 27 := ⟨1, by decide⟩

/-- The inverses of `1 … 26` (`0` is sent to `0`), by the table of the multiplication. -/
def invL : List ℕ :=
  [0, 1, 2, 19, 21, 24, 11, 12, 15, 25, 23, 6, 7, 22, 18, 8, 20, 26, 14, 3, 16, 4, 13, 10, 5, 9, 17]

/-- The inverse of `x` in `GF(27)`. -/
def invF (x : Fin 27) : Fin 27 := ⟨invL.getD x.val 0 % 27, Nat.mod_lt _ (by decide)⟩

theorem addF_assoc : ∀ a b c : Fin 27, addF (addF a b) c = addF a (addF b c) := by
  decide +kernel

theorem addF_comm : ∀ a b : Fin 27, addF a b = addF b a := by
  decide +kernel

theorem addF_zero : ∀ a : Fin 27, addF a zeroF = a := by
  decide +kernel

theorem zero_addF : ∀ a : Fin 27, addF zeroF a = a := by
  decide +kernel

theorem negF_add : ∀ a : Fin 27, addF (negF a) a = zeroF := by
  decide +kernel

theorem mulF_assoc : ∀ a b c : Fin 27, mulF (mulF a b) c = mulF a (mulF b c) := by
  decide +kernel

theorem mulF_comm : ∀ a b : Fin 27, mulF a b = mulF b a := by
  decide +kernel

theorem mulF_one : ∀ a : Fin 27, mulF a oneF = a := by
  decide +kernel

theorem one_mulF : ∀ a : Fin 27, mulF oneF a = a := by
  decide +kernel

theorem zero_mulF : ∀ a : Fin 27, mulF zeroF a = zeroF := by
  decide +kernel

theorem mul_zeroF : ∀ a : Fin 27, mulF a zeroF = zeroF := by
  decide +kernel

theorem left_distribF : ∀ a b c : Fin 27, mulF a (addF b c) = addF (mulF a b) (mulF a c) := by
  decide +kernel

theorem right_distribF : ∀ a b c : Fin 27, mulF (addF a b) c = addF (mulF a c) (mulF b c) := by
  decide +kernel

theorem mul_invF : ∀ x : Fin 27, x ≠ 0 → mulF x (invF x) = oneF := by
  decide +kernel

theorem mul_eq_one_invF : ∀ x y : Fin 27, mulF x y = oneF → invF x = y := by
  decide +kernel

instance : Zero F27 := ⟨zeroF⟩
instance : One F27 := ⟨oneF⟩
instance : Add F27 := ⟨addF⟩
instance : Mul F27 := ⟨mulF⟩
instance : Neg F27 := ⟨negF⟩
instance : NatCast F27 := ⟨Nat.unaryCast⟩
instance : IntCast F27 := ⟨Int.castDef⟩

/-- `GF(27)` is a commutative ring with these operations. -/
instance : CommRing F27 where
  add_assoc := addF_assoc
  zero_add := zero_addF
  add_zero := addF_zero
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := negF_add
  add_comm := addF_comm
  mul_assoc := mulF_assoc
  one_mul := one_mulF
  mul_one := mulF_one
  natCast_zero := rfl
  natCast_succ := fun _ => rfl
  intCast_ofNat := fun _ => rfl
  intCast_negSucc := fun _ => rfl
  left_distrib := left_distribF
  right_distrib := right_distribF
  zero_mul := zero_mulF
  mul_zero := mul_zeroF
  mul_comm := mulF_comm

end BipartiteDD.Haar.D9D8b
