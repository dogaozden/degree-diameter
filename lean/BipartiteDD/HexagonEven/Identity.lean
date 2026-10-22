import BipartiteDD.HexagonEven.Pi

/-! Theorem D (even `q`), algebraic core, part 1 (mirror of `HexagonD/Identity/Jz.lean`): the complex structure
`J` of the hyperplane `Π_z : x₀ + x₃ + d x₄ + α x₂ + β x₅ = 0` in characteristic `2`, with `t² + t + d` anisotropic.

`JE d α β x` is the vector of `F⁷` whose coordinates `0,1,2,4,5,6` are the formula for `J_z` of
`research/evenq/evenq.tex` (in the coordinates `x = (x₀,x₁,x₂,x₄,x₅,x₆)` of `Π_z`), and whose coordinate `3` is
`x₀ + d x₄ + α x₂ + β x₅`, so that `JE x ∈ Π_z`. Each identity is a polynomial identity modulo `2`: after
substituting `x₃` from `Π_z`, the difference of the two sides is `2 G` for an explicit integer polynomial `G`
(computed with sympy, as in `research/evenq/proof_J.py`), and `linear_combination G * h2` closes it.

Main results (for `x ∈ Π_z`):
* `JE_JE`: `J (J x) = J x + d • x`;
* `Qf_JE`: `Q(J x) = d Q(x)`; `Bf_JE`: `B(x, J x) = Q(x)`;
* `tits_JE`: the six Tits differences of `(x, J x)` are `Q(x)` times `1, 0, 0, d, α, β`;
* `isHPair_JE`, `exists_hline_JE` (in `Identity.lean`): `⟨x, J x⟩` is a line of `H(q)` in `Π_z`. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The hyperplane `Π_z` (characteristic `2`): `x₀ + x₃ + d x₄ + α x₂ + β x₅ = 0`. -/
def InPiZE (d α β : F) (x : V7 F) : Prop := x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0

def JA (d α β : F) (x : V7 F) : F := (d + 1) * x 0 + d * α * x 2 + d ^ 2 * x 4 + (α + d * β) * x 5
def JB (d α β : F) (x : V7 F) : F := β * x 0 + x 1 + α * β * x 2 + (α + d * β) * x 4 + β ^ 2 * x 5 + x 6
def JC (x : V7 F) : F := x 2 + x 5
def JD (d α β : F) (x : V7 F) : F := x 0 + (α + β) * x 2 + d * x 4 + β * x 5
def JF (d : F) (x : V7 F) : F := d * x 2
def JG (d α β : F) (x : V7 F) : F := (α + β) * x 0 + d * x 1 + α ^ 2 * x 2 + d * α * x 4 + α * β * x 5

/-- The complex structure `J` (a vector of `F⁷`; coordinate `3` fixed by `Π_z`). -/
def JE (d α β : F) (x : V7 F) : V7 F :=
  ![JA d α β x, JB d α β x, JC x, JA d α β x + d * JD d α β x + α * JC x + β * JF d x,
    JD d α β x, JF d x, JG d α β x]

theorem JE_smul (d α β c : F) (x : V7 F) : JE d α β (c • x) = c • JE d α β x := by
  funext i
  fin_cases i <;> simp [JE, JA, JB, JC, JD, JF, JG] <;> ring

theorem InPiZE_JE (d α β : F) (x : V7 F) (h2 : (2 : F) = 0) : InPiZE d α β (JE d α β x) := by
  unfold InPiZE
  simp only [JE, JA, JB, JC, JD, JF, JG]
  simp
  linear_combination (((d + 1) * x 0 + d * α * x 2 + d ^ 2 * x 4 + (α + d * β) * x 5) + d * (x 0 + (α + β) * x 2 + d * x 4 + β * x 5) + α * (x 2 + x 5) + β * (d * x 2)) * h2

/-- `J² = J + d` on `Π_z` (i.e. `J² + J + d = 0`). -/
theorem JE_JE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) :
    JE d α β (JE d α β x) = JE d α β x + d • x := by
  have e3 : x 3 = x 0 + d * x 4 + α * x 2 + β * x 5 := by
    unfold InPiZE at hx
    linear_combination hx - (x 0 + d * x 4 + α * x 2 + β * x 5) * h2
  funext i
  fin_cases i
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (α*d^2*x 2 + α*d*x 2 + α*d*x 5 + β*d^2*x 2 + β*d^2*x 5 + d^3*x 4 + d^2*x 0) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (α^2*x 2 + α*β*d*x 2 + α*β*x 2 + 2*α*β*x 5 + α*d*x 4 + α*x 0 + β^2*d*x 2 + β^2*d*x 5 + β*d^2*x 4 + β*d*x 0 + β*x 0) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (0) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (2*α*d^2*x 2 + α*d*x 2 + 2*α*d*x 5 + 2*β*d^2*x 2 + 2*β*d^2*x 5 + 2*d^3*x 4 + 2*d^2*x 0 - d^2*x 4) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (α*d*x 2 + α*x 5 + β*d*x 2 + β*d*x 5 + d^2*x 4 + d*x 0 - d*x 4) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (0) * h2
  · simp [JE, JA, JB, JC, JD, JF, JG, e3] <;> linear_combination (α^2*d*x 2 + α^2*x 5 + 2*α*β*d*x 2 + α*β*d*x 5 + α*d^2*x 4 + α*d*x 0 + β^2*d*x 5 + β*d^2*x 4 + β*d*x 0) * h2

/-- `Q(J x) = d Q(x)` on `Π_z`. -/
theorem Qf_JE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) :
    Qf (JE d α β x) = d * Qf x := by
  have e3 : x 3 = x 0 + d * x 4 + α * x 2 + β * x 5 := by
    unfold InPiZE at hx
    linear_combination hx - (x 0 + d * x 4 + α * x 2 + β * x 5) * h2
  simp [Qf, JE, JA, JB, JC, JD, JF, JG, e3]
  linear_combination (-2*α^2*d^2*x 2^2 - α^2*d*x 2^2 - 4*α^2*d*x 2*x 5 - α^2*x 2*x 5 - 2*α^2*x 5^2 - 4*α*β*d^2*x 2^2 - 4*α*β*d^2*x 2*x 5 - α*β*d*x 2^2 - 4*α*β*d*x 2*x 5 - 4*α*β*d*x 5^2 + α*β*x 2*x 5 + α*β*x 5^2 - 4*α*d^3*x 2*x 4 - 4*α*d^2*x 0*x 2 - 4*α*d^2*x 4*x 5 - 2*α*d*x 0*x 2 - 4*α*d*x 0*x 5 + α*d*x 2*x 4 + α*d*x 4*x 5 - α*x 0*x 5 - 2*β^2*d^2*x 2^2 - 4*β^2*d^2*x 2*x 5 - 2*β^2*d^2*x 5^2 + β^2*d*x 2*x 5 + β^2*d*x 5^2 - 4*β*d^3*x 2*x 4 - 4*β*d^3*x 4*x 5 - 4*β*d^2*x 0*x 2 - 4*β*d^2*x 0*x 5 + β*d^2*x 2*x 4 + 2*β*d^2*x 4*x 5 - β*d*x 0*x 2 + β*x 0*x 2 + β*x 0*x 5 - 2*d^4*x 4^2 - 4*d^3*x 0*x 4 + d^3*x 4^2 - 2*d^2*x 0^2 - d*x 0^2 + d*x 1*x 2) * h2

/-- `B(x, J x) = Q(x)` on `Π_z`. -/
theorem Bf_JE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) :
    Bf x (JE d α β x) = Qf x := by
  have e3 : x 3 = x 0 + d * x 4 + α * x 2 + β * x 5 := by
    unfold InPiZE at hx
    linear_combination hx - (x 0 + d * x 4 + α * x 2 + β * x 5) * h2
  simp [Bf, Qf, JE, JA, JB, JC, JD, JF, JG, e3]
  linear_combination (-2*α^2*d*x 2^2 - 2*α^2*x 2*x 5 - 2*α*β*d*x 2^2 - 4*α*β*d*x 2*x 5 + α*β*x 2*x 5 - 2*α*β*x 5^2 - 4*α*d^2*x 2*x 4 - 4*α*d*x 0*x 2 + α*d*x 2*x 4 - 2*α*d*x 4*x 5 - 2*α*x 0*x 5 + α*x 4*x 5 - 2*β^2*d*x 2*x 5 - 2*β^2*d*x 5^2 + β^2*x 5^2 - 2*β*d^2*x 2*x 4 - 4*β*d^2*x 4*x 5 - 2*β*d*x 0*x 2 - 4*β*d*x 0*x 5 + 2*β*d*x 4*x 5 + β*x 0*x 2 + β*x 0*x 5 - 2*d^3*x 4^2 - 4*d^2*x 0*x 4 + d^2*x 4^2 - 2*d*x 0^2 + d*x 0*x 4 + d*x 1*x 2 + x 5*x 6) * h2

/-- The six Tits differences of `(x, J x)` are `Q(x)` times `1, 0, 0, d, α, β`. -/
theorem tits_JE {d α β : F} {x : V7 F} (hx : InPiZE d α β x) (h2 : (2 : F) = 0) (hQ : Qf x = 0) :
    Tits x (JE d α β x) := by
  have e3 : x 3 = x 0 + d * x 4 + α * x 2 + β * x 5 := by
    unfold InPiZE at hx
    linear_combination hx - (x 0 + d * x 4 + α * x 2 + β * x 5) * h2
  have hQ' : x 0 * x 4 + x 1 * x 5 + x 2 * x 6 - x 3 ^ 2 = 0 := hQ
  rw [e3] at hQ'
  simp [Tits, pl, JE, JA, JB, JC, JD, JF, JG, e3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination (1) * hQ' + (-α*β*x 2^2 + α*d*x 2*x 4 + α*x 4*x 5 - β^2*x 2*x 5 + β*d*x 4*x 5 - β*x 0*x 2 + d^2*x 4^2 + d*x 0*x 4 - x 2*x 6) * h2
  · linear_combination (0) * hQ' + (α*d*x 2^2 + α*x 2*x 5 + β*d*x 2^2 + β*d*x 2*x 5 + d^2*x 2*x 4 + d*x 0*x 2 - d*x 2*x 4) * h2
  · linear_combination (0) * hQ' + (α*d*x 2*x 5 + α*x 2*x 5 + α*x 5^2 + β*d*x 2*x 5 + β*d*x 5^2 + d^2*x 4*x 5 + d*x 0*x 5) * h2
  · linear_combination (d) * hQ' + (-α^2*x 2*x 5 - α*β*x 5^2 + α*d*x 0*x 2 - α*d*x 4*x 5 + β*d*x 0*x 2 + β*d*x 0*x 5 - β*x 0*x 5 + d^2*x 0*x 4 + d*x 0^2 - d*x 0*x 4 - d*x 1*x 5) * h2
  · linear_combination (α) * hQ' + (-α*d*x 1*x 2 + α*d*x 2*x 6 - α*x 1*x 5 + α*x 5*x 6 - β*d*x 1*x 5 + β*d*x 2*x 6 + β*d*x 5*x 6 - d^2*x 1*x 4 + d^2*x 4*x 6 - d*x 0*x 1 + d*x 0*x 6 + x 0*x 6) * h2
  · linear_combination (β) * hQ' + (α*d*x 1*x 2 + α*x 1*x 5 - α*x 2*x 6 + β*d*x 1*x 2 + β*d*x 1*x 5 - β*x 1*x 5 - β*x 2*x 6 - β*x 5*x 6 + d^2*x 1*x 4 + d*x 0*x 1 - d*x 4*x 6 - x 0*x 6) * h2
