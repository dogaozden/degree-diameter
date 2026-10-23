import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.D7D9b.Cover

/-! The (7,9) record on 462840 vertices: the Haar graph of `PSL(2, 29) × Z_19` with the connection set of
`research/frontier/sols/d7D9_psl_29_19_orb3_s1.txt`. The covering hypotheses are the kernel-checked certificates of
`D7D9b.Cover`, built from the stage modules `D7D9b.Stage00 … Stage41`. -/

open BipartiteDD.Haar.D7D9b in
set_option maxHeartbeats 1000000 in
/-- A graph on 462840 vertices, bipartite, of degree at most 7 and diameter at most 9. -/
theorem nb_7_9_haar_462840 : ∃ G : SimpleGraph (Fin 462840), BipartiteDD.IsBipartiteDegDiam G 7 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS haarVert ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
