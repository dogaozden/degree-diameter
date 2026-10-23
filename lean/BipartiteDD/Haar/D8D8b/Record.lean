import BipartiteDD.Haar.D8D8b.Covers
import BipartiteDD.Haar.D7D8.Diam8

/-! The Δ8·D8 record `239,904`: degree `8`, diameter `8`, from the Haar graph of `PSL(2, 17) × Z49` with the
set `S` of `research/frontier/sols/d8D8_psl_17_49_orb3_s1.txt`. -/

open BipartiteDD.Haar.D8D8b in
/-- A bipartite graph on `239904` vertices with degree at most `8` and diameter at most `8`. -/
theorem BipartiteDD.Haar.D8D8b.nb_8_8 : ∃ H : SimpleGraph (Fin 239904), BipartiteDD.IsBipartiteDegDiam H 8 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_equiv SS haarVert
    ⟨sG 0, sG_mem (by norm_num)⟩ coverAA coverBB coverAB
  rw [card_SS] at h
  exact ⟨_, h⟩
