import BipartiteDD.Hexagon.Main

/-! Target 1 of `docs/lean-evenq-brief.md`: the split Cayley hexagon `H(q)` is a generalized hexagon over
every finite field, including those of characteristic `2`.

The odd-characteristic hypothesis `[NeZero (2 : F)]` used on master was needed only for the upper bound
`dim π_x ≤ 3` (`Hexagon.finrank_plane_le`). That bound now comes from the radical of the polar form `Bf`
(the line `⟨e₃⟩` in characteristic `2`, which meets the singular vectors trivially) and holds for every field.
So the master theorem `Hexagon.genPolygonGraph_hexagon` is already stated for all finite fields; this file
records that statement for the even-`q` slice. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon

variable (F : Type*) [Field F] [Fintype F]

/-- `H(q)` is a generalized hexagon for every finite field `F` with `q = |F|` elements. -/
theorem hexagon_all : BipartiteDD.Doubling.GenPolygonGraph (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) 6 :=
  genPolygonGraph_hexagon

end BipartiteDD.HexagonEven
