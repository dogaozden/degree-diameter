import BipartiteDD.HexagonEven.Main

/-! Sanity checks in characteristic `2` (where the old `NeZero (2 : F)` route is unavailable). -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon

theorem hexagon_q2 :
    BipartiteDD.Doubling.GenPolygonGraph (BipartiteDD.Hexagon.incGraph (hexInc (F := ZMod 2))) 6 :=
  genPolygonGraph_hexagon_even

theorem card_spt_q2 : Nat.card (SPt (ZMod 2)) = 63 := by
  rw [card_spt_eq, ZMod.card]
  norm_num

end BipartiteDD.HexagonEven
