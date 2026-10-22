import BipartiteDD.HexagonEven.Main

/-! Sanity checks for even `q`: `H(2)` (characteristic `2`). The general theorem `hexagon_all` is instantiated at
`ZMod 2`, and a kernel-checked (`decide +kernel`, no native code) count of the singular vectors for `q = 2`. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon

/-- `H(2)` is a generalized hexagon (characteristic `2`). -/
theorem hexagon_q2 : BipartiteDD.Doubling.GenPolygonGraph (BipartiteDD.Hexagon.incGraph (hexInc (F := ZMod 2))) 6 :=
  hexagon_all (ZMod 2)

/-- `H(2)` has `63 = (2⁶-1)/1` points. -/
theorem card_spt_q2 : Nat.card (SPt (ZMod 2)) = 63 := by
  rw [card_spt_eq]; simp [ZMod.card]

/-- Direct computation for `q = 2`: `2⁶ = 64` singular vectors in `(ZMod 2)⁷`. -/
theorem card_zeros_q2 : Fintype.card {x : V7 (ZMod 2) // Qf x = 0} = 64 := by
  decide +kernel

end BipartiteDD.HexagonEven
