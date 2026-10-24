import BipartiteDD.Haar.D6D8d.Covers
import BipartiteDD.Haar.D7D8.Diam8

/-! The Δ6·D8 record `31,680`: degree `6`, diameter `8`, from the Haar graph of `PSL(2, 11) × Z24` with the set `S`
of `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`. The diameter-8 lemma is `Haar.isBipartiteDegDiam_eight_equiv`,
shared with the `88,920` and `95,760` records. -/

open BipartiteDD.Haar.D6D8d in
/-- A bipartite graph on `31680` vertices with degree at most `6` and diameter at most `8`. -/
theorem nb_6_8_31680 : ∃ H : SimpleGraph (Fin 31680), BipartiteDD.IsBipartiteDegDiam H 6 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_equiv SS haarVert
    ⟨sG 0, sG_mem (by norm_num)⟩ coverAA coverBB coverAB
  rw [card_SS] at h
  exact ⟨_, h⟩
