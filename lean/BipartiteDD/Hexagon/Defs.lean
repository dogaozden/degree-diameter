import Mathlib

/-! Split Cayley hexagon `H(q)`, part 1: the parabolic quadric `Q(6, q)` and Tits' equations.

Over a field `F` the quadric form on `F^7` is `Q x = x₀x₄ + x₁x₅ + x₂x₆ - x₃²`, with polar form
`B x y = Q (x + y) - Q x - Q y`. The lines of `H(q)` are the totally singular lines `⟨x, y⟩` whose Grassmann
coordinates `p_ij = x_i y_j - x_j y_i` satisfy Tits' six equations (the ones of `research/gh6/gh_build.py`)
  `p₁₂ = p₃₄, p₅₄ = p₃₂, p₂₀ = p₃₅, p₆₅ = p₃₀, p₀₁ = p₃₆, p₄₆ = p₃₁`.
`IsHPair x y` is this predicate on a pair of vectors; `HLine F` collects the 2-dimensional subspaces all of
whose pairs satisfy it. -/

namespace BipartiteDD.Hexagon

open Module

variable (F : Type*) [Field F]

/-- The vector space `F^7` carrying the quadric. -/
abbrev V7 := Fin 7 → F

variable {F}

/-- The parabolic quadric form `Q(x) = x₀x₄ + x₁x₅ + x₂x₆ - x₃²`. -/
def Qf (x : V7 F) : F := x 0 * x 4 + x 1 * x 5 + x 2 * x 6 - x 3 ^ 2

/-- Its polar form `B(x, y) = Q(x + y) - Q(x) - Q(y)`. -/
def Bf (x y : V7 F) : F :=
  x 0 * y 4 + x 4 * y 0 + x 1 * y 5 + x 5 * y 1 + x 2 * y 6 + x 6 * y 2 - 2 * (x 3 * y 3)

/-- Grassmann coordinate `p_ij = x_i y_j - x_j y_i`. -/
def pl (x y : V7 F) (i j : Fin 7) : F := x i * y j - x j * y i

/-- Tits' six equations on the Grassmann coordinates of the pair `(x, y)`. -/
def Tits (x y : V7 F) : Prop :=
  pl x y 1 2 = pl x y 3 4 ∧ pl x y 5 4 = pl x y 3 2 ∧ pl x y 2 0 = pl x y 3 5 ∧
  pl x y 6 5 = pl x y 3 0 ∧ pl x y 0 1 = pl x y 3 6 ∧ pl x y 4 6 = pl x y 3 1

/-- The pair `(x, y)` spans a totally singular line satisfying Tits' equations. -/
def IsHPair (x y : V7 F) : Prop := Qf x = 0 ∧ Qf y = 0 ∧ Bf x y = 0 ∧ Tits x y

theorem Qf_add (x y : V7 F) : Qf (x + y) = Qf x + Qf y + Bf x y := by
  simp only [Qf, Bf, Pi.add_apply]; ring

theorem Qf_smul (c : F) (x : V7 F) : Qf (c • x) = c ^ 2 * Qf x := by
  simp only [Qf, Pi.smul_apply, smul_eq_mul]; ring

theorem Bf_comm (x y : V7 F) : Bf x y = Bf y x := by
  simp only [Bf]; ring

theorem Tits.symm {x y : V7 F} (h : Tits x y) : Tits y x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [Tits, pl] at *
  exact ⟨by linear_combination -h1, by linear_combination -h2, by linear_combination -h3,
    by linear_combination -h4, by linear_combination -h5, by linear_combination -h6⟩

theorem IsHPair.symm {x y : V7 F} (h : IsHPair x y) : IsHPair y x :=
  ⟨h.2.1, h.1, by rw [Bf_comm]; exact h.2.2.1, h.2.2.2.symm⟩

/-- Singular points of `Q(6, q)`: points of `PG(6, F)` on the quadric. -/
abbrev SPt (F : Type*) [Field F] := {p : Projectivization F (V7 F) // Qf p.rep = 0}

/-- Lines of `H(q)`: 2-dimensional subspaces of `F^7` all of whose pairs satisfy Tits' equations. -/
def HLine (F : Type*) [Field F] : Type _ :=
  {W : Submodule F (V7 F) // finrank F W = 2 ∧ ∀ x ∈ W, ∀ y ∈ W, IsHPair x y}

end BipartiteDD.Hexagon
