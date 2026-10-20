import BipartiteDD.Hexagon.Main

/-! Sanity checks for `H(3)` and `H(5)`: the general theorems instantiated at `ZMod 3` and `ZMod 5`, and
a kernel-checked (`decide +kernel`, no native code) count of the singular vectors for `q = 3`. -/

namespace BipartiteDD.Hexagon

instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : NeZero (2 : ZMod 3) := ⟨by decide⟩
instance : NeZero (2 : ZMod 5) := ⟨by decide⟩

theorem hexagon_q3 : BipartiteDD.Doubling.GenPolygonGraph (incGraph (hexInc (F := ZMod 3))) 6 :=
  genPolygonGraph_hexagon

theorem hexagon_q5 : BipartiteDD.Doubling.GenPolygonGraph (incGraph (hexInc (F := ZMod 5))) 6 :=
  genPolygonGraph_hexagon

/-- `H(3)` has `364 = (3⁶-1)/2` points. -/
theorem card_spt_q3 : Nat.card (SPt (ZMod 3)) = 364 := by
  rw [card_spt_eq]; simp [ZMod.card]

/-- `H(5)` has `3906 = (5⁶-1)/4` points. -/
theorem card_spt_q5 : Nat.card (SPt (ZMod 5)) = 3906 := by
  rw [card_spt_eq]; simp [ZMod.card]

/-- Direct computation for `q = 3`: `3⁶ = 729` singular vectors in `(ZMod 3)⁷`. -/
theorem card_zeros_q3 : Fintype.card {x : V7 (ZMod 3) // Qf x = 0} = 729 := by
  decide +kernel

end BipartiteDD.Hexagon

