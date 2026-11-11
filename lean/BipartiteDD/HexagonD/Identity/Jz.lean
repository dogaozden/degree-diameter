import BipartiteDD.HexagonD.Pi

/-! Theorem D, algebraic core, part 1: the complex structure `J_z` on the hyperplane `Π_z`.

For `z = (α, β)` the hyperplane is `Π_z = {x | x₀ + c x₄ + α x₂ + β x₅ = 0}`; `z = 0` gives `Π`. A point of `Π_z`
is determined by its coordinates `x₁, …, x₆`, and there
`J_z x = (-β x₃ + α x₄ - x₆, x₅, -c x₄ - β x₅, x₃ + β x₂, -c x₂, c x₁ + αβ x₂ + α x₃ + cβ x₄ + β² x₅)`
in coordinates `1, …, 6`, with coordinate `0` forced by `Π_z`, namely `-c y₄ - α y₂ - β y₅`.
`Jz` below is that vector of `F^7`; it reads only the coordinates `1, …, 6` of its argument.

Main results, for `x ∈ Π_z`:
* `Jz_Jz`: `J_z (J_z x) = -c x`;
* `Qf_Jz`: `Q(J_z x) = c Q(x)`;
* `Bf_Jz`: `B(x, J_z x) = 0`;
* `tits_Jz`: the six Tits differences of `(x, J_z x)` are `Q(x)` times `1, 0, 0, -c, α, -β`. -/

namespace BipartiteDD.HexagonD.Identity

open BipartiteDD.Hexagon

variable {F : Type*} [Field F]

/-- The hyperplane `Π_z`, `z = (α, β)`. -/
def InPiz (c α β : F) (x : V7 F) : Prop := x 0 + c * x 4 + α * x 2 + β * x 5 = 0

/-- The complex structure `J_z` of `Π_z`, as a vector of `F^7`. -/
def Jz (c α β : F) (x : V7 F) : V7 F :=
  ![-c * (x 3 + β * x 2) - α * x 5 + c * β * x 2, -β * x 3 + α * x 4 - x 6, x 5, -c * x 4 - β * x 5,
    x 3 + β * x 2, -c * x 2, c * x 1 + α * β * x 2 + α * x 3 + c * β * x 4 + β ^ 2 * x 5]

theorem Jz_0 (c α β : F) (x : V7 F) :
    Jz c α β x 0 = -c * (x 3 + β * x 2) - α * x 5 + c * β * x 2 := rfl

theorem Jz_1 (c α β : F) (x : V7 F) : Jz c α β x 1 = -β * x 3 + α * x 4 - x 6 := rfl

theorem Jz_2 (c α β : F) (x : V7 F) : Jz c α β x 2 = x 5 := rfl

theorem Jz_3 (c α β : F) (x : V7 F) : Jz c α β x 3 = -c * x 4 - β * x 5 := rfl

theorem Jz_4 (c α β : F) (x : V7 F) : Jz c α β x 4 = x 3 + β * x 2 := rfl

theorem Jz_5 (c α β : F) (x : V7 F) : Jz c α β x 5 = -c * x 2 := rfl

theorem Jz_6 (c α β : F) (x : V7 F) :
    Jz c α β x 6 = c * x 1 + α * β * x 2 + α * x 3 + c * β * x 4 + β ^ 2 * x 5 := rfl

/-- Coordinate `0` of a point of `Π_z`, solved from the equation of `Π_z`. -/
theorem coord0 {c α β : F} {x : V7 F} (hx : InPiz c α β x) : x 0 = -c * x 4 - α * x 2 - β * x 5 := by
  unfold InPiz at hx
  linear_combination hx

theorem InPiz_Jz (c α β : F) (x : V7 F) : InPiz c α β (Jz c α β x) := by
  unfold InPiz
  rw [Jz_0, Jz_2, Jz_4, Jz_5]
  ring

theorem Jz_smul (c α β a : F) (x : V7 F) : Jz c α β (a • x) = a • Jz c α β x := by
  funext i
  fin_cases i <;> simp [Jz] <;> ring

theorem Qf_Jz {c α β : F} {x : V7 F} (hx : InPiz c α β x) : Qf (Jz c α β x) = c * Qf x := by
  simp only [Qf, Jz_0, Jz_1, Jz_2, Jz_3, Jz_4, Jz_5, Jz_6, coord0 hx]
  ring

theorem Bf_Jz {c α β : F} {x : V7 F} (hx : InPiz c α β x) : Bf x (Jz c α β x) = 0 := by
  simp only [Bf, Jz_0, Jz_1, Jz_2, Jz_3, Jz_4, Jz_5, Jz_6, coord0 hx]
  ring

/-- The six Tits differences of `(x, J_z x)`, for `x ∈ Π_z`. -/
theorem tits_Jz {c α β : F} {x : V7 F} (hx : InPiz c α β x) :
    pl x (Jz c α β x) 1 2 - pl x (Jz c α β x) 3 4 = Qf x ∧
    pl x (Jz c α β x) 5 4 - pl x (Jz c α β x) 3 2 = 0 ∧
    pl x (Jz c α β x) 2 0 - pl x (Jz c α β x) 3 5 = 0 ∧
    pl x (Jz c α β x) 6 5 - pl x (Jz c α β x) 3 0 = -c * Qf x ∧
    pl x (Jz c α β x) 0 1 - pl x (Jz c α β x) 3 6 = α * Qf x ∧
    pl x (Jz c α β x) 4 6 - pl x (Jz c α β x) 3 1 = -β * Qf x := by
  simp only [pl, Qf, Jz_0, Jz_1, Jz_2, Jz_3, Jz_4, Jz_5, Jz_6, coord0 hx]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

theorem Jz_Jz {c α β : F} {x : V7 F} (hx : InPiz c α β x) : Jz c α β (Jz c α β x) = -c • x := by
  funext i
  fin_cases i <;> simp [Jz, coord0 hx] <;> ring

end BipartiteDD.HexagonD.Identity
