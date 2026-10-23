import BipartiteDD.Haar.D7D8b.Covers
import BipartiteDD.Haar.D7D8.Diam8

/-! The Δ7·D8 record `95,760`: degree `7`, diameter `8`, from the Haar graph of `PSL(2, 19) × Z14` with the set `S`
of `research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt`. The diameter-8 lemma is `Haar.D7D8.Diam8`, shared with
the `88,920` record. -/

open BipartiteDD.Haar.D7D8b in
/-- A bipartite graph on `95760` vertices with degree at most `7` and diameter at most `8`. -/
theorem nb_7_8_b : ∃ H : SimpleGraph (Fin 95760), BipartiteDD.IsBipartiteDegDiam H 7 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_equiv SS haarVert
    ⟨sG 0, sG_mem (by norm_num)⟩ coverAA coverBB coverAB
  rw [card_SS] at h
  exact ⟨_, h⟩
