import BipartiteDD.Haar.D6D10d.Covering
import BipartiteDD.Haar.Diam10

/-! The (6,10) record on 524,160 vertices: the Haar graph of `SL(2,5) × PSL(2,7) × Z_13` with the connection set `S`
of `research/frontier/sols/d6D10_prod_sl_5_psl_7_13_orb3f0_s1.txt`. The covering hypothesis is `D6D10d.cover`. -/

open BipartiteDD.Haar.D6D10d in
/-- A graph on 524160 vertices, bipartite, of degree at most 6 and diameter at most 10. -/
theorem nb_6_10_524160 : ∃ G : SimpleGraph (Fin 524160), BipartiteDD.IsBipartiteDegDiam G 6 10 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv SS haarVert cover
  rw [card_SS] at h
  exact ⟨_, h⟩
