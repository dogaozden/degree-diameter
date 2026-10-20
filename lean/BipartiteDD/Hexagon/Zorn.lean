import BipartiteDD.Hexagon.Defs

/-! Split Cayley hexagon `H(q)`, part 2: the Zorn algebra of split octonions.

An element of the split octonion algebra is a vector-matrix `(a, u; v, b)` with `a, b ∈ F`, `u, v ∈ F³`,
stored as `Fin 8 → F` in the order `a, b, u₀, u₁, u₂, v₀, v₁, v₂`. The product is
`(a, u; v, b)(a', u'; v', b') = (aa' + u·v', a u' + b' u - v × v'; a' v + b v' + u × u', bb' + v·u')`
and the norm is `N(a, u; v, b) = ab - u·v`. The trace-zero part is embedded from `F^7` by
`φ x = (x₃, -x₃; u = -(x₀, x₁, x₂), v = (x₄, x₅, x₆))`, so that `N (φ x) = Qf x`; with this sign choice the six
vector components of `φ x · φ y` are exactly the differences of Tits' equations (`Tits`).

All identities are polynomial identities proved by `ring`. -/

namespace BipartiteDD.Hexagon

variable {F : Type*} [Field F]

/-- Split octonions (Zorn vector-matrices) as `Fin 8 → F`. -/
abbrev C8 (F : Type*) := Fin 8 → F

/-- The Zorn product. -/
def zmul (x y : C8 F) : C8 F := ![
  x 0 * y 0 + (x 2 * y 5 + x 3 * y 6 + x 4 * y 7),
  x 1 * y 1 + (x 5 * y 2 + x 6 * y 3 + x 7 * y 4),
  x 0 * y 2 + y 1 * x 2 - (x 6 * y 7 - x 7 * y 6),
  x 0 * y 3 + y 1 * x 3 - (x 7 * y 5 - x 5 * y 7),
  x 0 * y 4 + y 1 * x 4 - (x 5 * y 6 - x 6 * y 5),
  y 0 * x 5 + x 1 * y 5 + (x 3 * y 4 - x 4 * y 3),
  y 0 * x 6 + x 1 * y 6 + (x 4 * y 2 - x 2 * y 4),
  y 0 * x 7 + x 1 * y 7 + (x 2 * y 3 - x 3 * y 2)]

/-- The norm `N(a, u; v, b) = ab - u·v`. -/
def Nf (x : C8 F) : F := x 0 * x 1 - (x 2 * x 5 + x 3 * x 6 + x 4 * x 7)

/-- The polar form of the norm. -/
def Bn (x y : C8 F) : F :=
  x 0 * y 1 + x 1 * y 0 - (x 2 * y 5 + x 5 * y 2 + x 3 * y 6 + x 6 * y 3 + x 4 * y 7 + x 7 * y 4)

/-- Conjugation `(a, u; v, b) ↦ (b, -u; -v, a)`. -/
def zconj (x : C8 F) : C8 F := ![x 1, x 0, -x 2, -x 3, -x 4, -x 5, -x 6, -x 7]

/-- The unit `(1, 0; 0, 1)`. -/
def zone : C8 F := ![1, 1, 0, 0, 0, 0, 0, 0]

/-- Embedding of `F^7` as the trace-zero part. -/
def phi (x : V7 F) : C8 F := ![x 3, -x 3, -x 0, -x 1, -x 2, x 4, x 5, x 6]

theorem Nf_phi (x : V7 F) : Nf (phi x) = Qf x := by
  simp [Nf, phi, Qf]; ring

theorem Bn_phi (x y : V7 F) : Bn (phi x) (phi y) = Bf x y := by
  simp [Bn, phi, Bf]; ring

theorem Nf_add (x y : C8 F) : Nf (x + y) = Nf x + Nf y + Bn x y := by
  simp only [Nf, Bn, Pi.add_apply]; ring

theorem Nf_smul (c : F) (x : C8 F) : Nf (c • x) = c ^ 2 * Nf x := by
  simp only [Nf, Pi.smul_apply, smul_eq_mul]; ring

/-- Composition: `N(xy) = N(x) N(y)`. -/
theorem Nf_zmul (x y : C8 F) : Nf (zmul x y) = Nf x * Nf y := by
  simp only [Nf, zmul]
  simp
  ring

/-- `(x y) ȳ = N(y) x`. -/
theorem zmul_zconj_right (x y : C8 F) : zmul (zmul x y) (zconj y) = Nf y • x := by
  ext k
  fin_cases k <;> simp [zmul, zconj, Nf] <;> ring

/-- `x̄ (x y) = N(x) y`. -/
theorem zmul_zconj_left (x y : C8 F) : zmul (zconj x) (zmul x y) = Nf x • y := by
  ext k
  fin_cases k <;> simp [zmul, zconj, Nf] <;> ring

/-- Left alternativity `x (x y) = (x x) y`. -/
theorem zmul_alt_left (x y : C8 F) : zmul x (zmul x y) = zmul (zmul x x) y := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

/-- Right alternativity `(x y) y = x (y y)`. -/
theorem zmul_alt_right (x y : C8 F) : zmul (zmul x y) y = zmul x (zmul y y) := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

/-- For trace-zero `φ x`, the square is `-N`. -/
theorem zmul_phi_self (x : V7 F) : zmul (phi x) (phi x) = (-Qf x) • zone := by
  ext k
  fin_cases k <;> simp [zmul, phi, zone, Qf] <;> ring

theorem zmul_add_right (x y z : C8 F) : zmul x (y + z) = zmul x y + zmul x z := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

theorem zmul_add_left (x y z : C8 F) : zmul (x + y) z = zmul x z + zmul y z := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

theorem zmul_smul_right (c : F) (x y : C8 F) : zmul x (c • y) = c • zmul x y := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

theorem zmul_smul_left (c : F) (x y : C8 F) : zmul (c • x) y = c • zmul x y := by
  ext k
  fin_cases k <;> simp [zmul] <;> ring

theorem phi_add (x y : V7 F) : phi (x + y) = phi x + phi y := by
  ext k; fin_cases k <;> simp [phi] <;> ring

theorem phi_smul (c : F) (x : V7 F) : phi (c • x) = c • phi x := by
  ext k; fin_cases k <;> simp [phi]

end BipartiteDD.Hexagon
