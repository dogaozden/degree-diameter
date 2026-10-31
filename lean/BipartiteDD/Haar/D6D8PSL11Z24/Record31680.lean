import BipartiteDD.Haar.Eight
import BipartiteDD.Haar.D6D8PSL11Z24.Cover

/-! The (6,8) record on 31680 vertices, as the Haar graph of `G = PSL(2,11) × Z24` (order 15840) with the connection set
`S` of `research/frontier/sols/d6D8_psl_11_24_orb2f0_s1.txt`. The covering hypotheses of the diameter-8 lemma `Eight.lean`
are the kernel-checked chunks of `D6D8PSL11Z24.Cover`. -/

open BipartiteDD.Haar.D6D8PSL11Z24 in
/-- A graph on 31680 vertices, bipartite, of degree at most 6 and diameter at most 8. -/
theorem nb_6_8_n31680 : ∃ G : SimpleGraph (Fin 31680), BipartiteDD.IsBipartiteDegDiam G 6 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_of SS
    ((BipartiteDD.Haar.haarGraph SS).comap haarVert.symm) haarVert
    (fun x y => by simp [SimpleGraph.comap_adj]) coverA coverB coverC
  rw [card_SS] at h
  exact ⟨_, h⟩
