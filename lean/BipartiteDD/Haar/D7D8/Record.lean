import BipartiteDD.Haar.D7D8.Covers
import BipartiteDD.Haar.D7D8.Diam8

/-! The Δ7·D8 record: `88,920` vertices, degree `7`, diameter `8`, from the Haar graph of
`PSL(2, 19) × Z13` with the set `S` of `research/frontier/sols/d7D8_psl_19_13_s403.txt`. -/

open BipartiteDD.Haar.D7D8 in
/-- A bipartite graph on `88920` vertices with degree at most `7` and diameter at most `8`. -/
theorem nb_7_8 : ∃ H : SimpleGraph (Fin 88920), BipartiteDD.IsBipartiteDegDiam H 7 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_equiv SS haarVert
    ⟨sG 0, sG_mem (by norm_num)⟩ coverAA coverBB coverAB
  rw [card_SS] at h
  exact ⟨_, h⟩
