import BipartiteDD.HexagonD.RegHex7

/-! Theorem D, slice 2, part 30 (target 5): **Theorem R** (regular graphs of diameter 6), final form.

For every finite field `F` of odd characteristic (`q = |F|`) and `m ≥ 2` there is a `(q + m)`-regular bipartite graph of
diameter at most `6` on `2 [(q + 1)(q⁴ + q² + 1) + (m - 1)((q³ + 1)(q + 1) + m (q + 1))]` vertices, i.e.
`2 (q + 1)[q⁴ + q² + 1 + (m - 1)(q³ + m + 1)]` (`research/p4/regular/REPORT.md`, Theorem R). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)]

theorem theoremR_hexagon {m : ℕ} (hm : 2 ≤ m) :
    ∃ G : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1))))),
      IsBipartiteRegDiam G (Fintype.card F + m) 6 := by
  classical
  obtain ⟨c, c0, c1, hc, hG, -⟩ := theorem4 (F := F)
  have h := theoremR (m := m) hc hG hm
  rw [card_VL_eq hc (by omega)] at h
  exact h

/-- `q + 2`: `2 (q + 1)(q⁴ + q³ + q² + 4)` vertices. -/
theorem theoremR_hexagon_two :
    ∃ G : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
        ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + 2 * (Fintype.card F + 1))))),
      IsBipartiteRegDiam G (Fintype.card F + 2) 6 := by
  have h := theoremR_hexagon (F := F) (m := 2) le_rfl
  rwa [show (2 - 1 : ℕ) = 1 from rfl, one_mul] at h

end BipartiteDD.HexagonD
