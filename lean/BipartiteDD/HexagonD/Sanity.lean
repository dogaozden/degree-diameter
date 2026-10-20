import BipartiteDD.HexagonD.Delorme

/-! Sanity checks: Delorme's bound for `q = 3` and `q = 5`. -/

namespace BipartiteDD.HexagonD

instance : NeZero (2 : ZMod 3) := ⟨by decide⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : NeZero (2 : ZMod 5) := ⟨by decide⟩

/-- `q = 3`: a bipartite graph of degree `≤ 5`, diameter `≤ 6` and `948` vertices. -/
example : ∃ H : SimpleGraph (Fin 948), IsBipartiteDegDiam H 5 6 := by
  have := delorme_bound_hexagon_two (F := ZMod 3)
  have e : 2 * ((Fintype.card (ZMod 3) + 1) * (1 + Fintype.card (ZMod 3) ^ 2 + Fintype.card (ZMod 3) ^ 4)) +
      (Fintype.card (ZMod 3) ^ 4 + 4 * Fintype.card (ZMod 3) ^ 3 + Fintype.card (ZMod 3) ^ 2 +
        4 * Fintype.card (ZMod 3) + 10) = 948 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

/-- `q = 5`: a bipartite graph of degree `≤ 7`, diameter `≤ 6` and `8992` vertices. -/
example : ∃ H : SimpleGraph (Fin 8992), IsBipartiteDegDiam H 7 6 := by
  have := delorme_bound_hexagon_two (F := ZMod 5)
  have e : 2 * ((Fintype.card (ZMod 5) + 1) * (1 + Fintype.card (ZMod 5) ^ 2 + Fintype.card (ZMod 5) ^ 4)) +
      (Fintype.card (ZMod 5) ^ 4 + 4 * Fintype.card (ZMod 5) ^ 3 + Fintype.card (ZMod 5) ^ 2 +
        4 * Fintype.card (ZMod 5) + 10) = 8992 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

end BipartiteDD.HexagonD
