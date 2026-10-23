import BipartiteDD.Haar.R225792.Enum
import BipartiteDD.Haar.R225792.TabData

/-! Definitions of the multiplication and inverse tables. Multiplication and inverse tables and inverse tables of `PSL(2,7)` and `SL(2,7)` (generated in `TabData.lean`), checked against
the group operations of `Enum.lean` by the kernel. The stage checks of `Check.lean` run on table indices, so
their cost is a few table lookups per letter instead of group products in `ZMod 7`. -/

namespace BipartiteDD.Haar.R225792

open M2

/-- The index `n mod 168` as an element of `Fin 168`. -/
def f168 (n : ℕ) : Fin 168 := ⟨n % 168, Nat.mod_lt _ (by norm_num)⟩

/-- The index `n mod 336` as an element of `Fin 336`. -/
def f336 (n : ℕ) : Fin 336 := ⟨n % 336, Nat.mod_lt _ (by norm_num)⟩

/-- The index `n mod 2` as an element of `Fin 2`. -/
def f2 (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by norm_num)⟩

theorem f168_val (x : Fin 168) : f168 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
theorem f336_val (x : Fin 336) : f336 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)
theorem f2_val (x : Fin 2) : f2 x.val = x := Fin.ext (Nat.mod_eq_of_lt x.isLt)

/-- Entry `(i, j)` of the PSL product table. -/
def mP (i j : ℕ) : ℕ := mProws.getD (i % 168) 0 / 2 ^ (8 * (j % 168)) % 256

/-- Entry `(i, j)` of the SL product table. -/
def mQ (i j : ℕ) : ℕ := mQrows.getD (i % 336) 0 / 2 ^ (9 * (j % 336)) % 512

/-- The PSL inverse table. -/
def iP (i : ℕ) : ℕ := iPtab / 2 ^ (8 * (i % 168)) % 256

/-- The SL inverse table. -/
def iQ (j : ℕ) : ℕ := iQtab / 2 ^ (9 * (j % 336)) % 512

def mPcheck (i : ℕ) : Bool :=
  (List.range 168).all fun j =>
    decide (pslAt (f168 (mP i j)) = canon (mul (pslAt (f168 i)) (pslAt (f168 j))))

def mQcheck (i : ℕ) : Bool :=
  (List.range 336).all fun j =>
    decide (slAt (f336 (mQ i j)) = mul (slAt (f336 i)) (slAt (f336 j)))

def iPcheck (i : ℕ) : Bool :=
  decide (pslAt (f168 (iP i)) = canon (adj (pslAt (f168 i))))

def iQcheck (j : ℕ) : Bool :=
  decide (slAt (f336 (iQ j)) = adj (slAt (f336 j)))

