import BipartiteDD.HexagonD.Delorme
import BipartiteDD.HexagonD.TheoremD
import BipartiteDD.HexagonD.TheoremR

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

/-- Theorem D for `q = 3`: `1020` vertices, degree `≤ 5`, diameter `≤ 6`. -/
example : ∃ H : SimpleGraph (Fin 1020), IsBipartiteDegDiam H 5 6 := by
  have := theoremD_two (F := ZMod 3)
  have e : 2 * ((Fintype.card (ZMod 3) + 1) * (1 + Fintype.card (ZMod 3) ^ 2 + Fintype.card (ZMod 3) ^ 4)) +
      (2 * Fintype.card (ZMod 3) ^ 4 + 4 * Fintype.card (ZMod 3) ^ 3 + 4 * Fintype.card (ZMod 3) + 10) =
      1020 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

/-- Theorem D for `q = 5`: `9592` vertices, degree `≤ 7`, diameter `≤ 6` (the record of the report). -/
example : ∃ H : SimpleGraph (Fin 9592), IsBipartiteDegDiam H 7 6 := by
  have := theoremD_two (F := ZMod 5)
  have e : 2 * ((Fintype.card (ZMod 5) + 1) * (1 + Fintype.card (ZMod 5) ^ 2 + Fintype.card (ZMod 5) ^ 4)) +
      (2 * Fintype.card (ZMod 5) ^ 4 + 4 * Fintype.card (ZMod 5) ^ 3 + 4 * Fintype.card (ZMod 5) + 10) =
      9592 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

/-- Theorem R for `q = 3`: a `5`-regular bipartite graph of diameter `≤ 6` on `968` vertices. -/
example : ∃ G : SimpleGraph (Fin 968), IsBipartiteRegDiam G 5 6 := by
  have := theoremR_hexagon_two (F := ZMod 3)
  have e : 2 * ((Fintype.card (ZMod 3) + 1) * (1 + Fintype.card (ZMod 3) ^ 2 + Fintype.card (ZMod 3) ^ 4) +
      ((Fintype.card (ZMod 3) ^ 3 + 1) * (Fintype.card (ZMod 3) + 1) + 2 * (Fintype.card (ZMod 3) + 1))) =
      968 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

/-- Theorem R for `q = 5`: a `7`-regular bipartite graph of diameter `≤ 6` on `9348` vertices. -/
example : ∃ G : SimpleGraph (Fin 9348), IsBipartiteRegDiam G 7 6 := by
  have := theoremR_hexagon_two (F := ZMod 5)
  have e : 2 * ((Fintype.card (ZMod 5) + 1) * (1 + Fintype.card (ZMod 5) ^ 2 + Fintype.card (ZMod 5) ^ 4) +
      ((Fintype.card (ZMod 5) ^ 3 + 1) * (Fintype.card (ZMod 5) + 1) + 2 * (Fintype.card (ZMod 5) + 1))) =
      9348 := by simp [ZMod.card]
  rw [e, ZMod.card] at this
  exact this

end BipartiteDD.HexagonD
