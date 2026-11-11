import BipartiteDD.Hexagon.Plane
import BipartiteDD.Hexagon.QuadricCount

/-!
# Omega45b: the `q = 7` case of the repair impossibility, concrete `H(7)`

Shared names. `F7 = ZMod 7` is the field of the concrete hexagon `H(7)`; vectors are `V7 F7 = Fin 7 → ZMod 7`
with the quadric `Qf` and polar form `Bf` of `BipartiteDD.Hexagon.Defs`.
-/

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon

/-- The field of `H(7)`. -/
abbrev F7 := ZMod 7

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The zeros of `Qf` in `F7^7` orthogonal (for `Bf`) to every vector of the list `S`. -/
def perpZeros (S : List (V7 F7)) : Finset (V7 F7) :=
  Finset.univ.filter fun x => Qf x = 0 ∧ ∀ s ∈ S, Bf x s = 0

end BipartiteDD.LeanMaxx.Omega45b
