import BipartiteDD.Haar.Eight
import BipartiteDD.Haar.D5D8N9760.Cover

/-! The (5,8) record on 9760 vertices, as the Haar graph of `G = C61 : C80` (y acts with order 80) with the connection set
`S` of `research/frontier/sols/d5D8_n9760_haar_meta61_80_8_s1.txt`. The covering hypotheses of the Haar lemma of
`Eight.lean` are the kernel-checked chunks of `D5D8N9760.Cover`. -/

namespace BipartiteDD.Haar.D5D8N9760

/-- `Grp ⊕ Grp ≃ Fin 9760`: the two sides of the Haar graph, numbered `0 … 9759`. -/
def equiv9760 : Grp ⊕ Grp ≃ Fin 9760 :=
  (Equiv.sumCongr equiv4880 equiv4880).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D5D8N9760

open BipartiteDD.Haar.D5D8N9760 in
/-- A graph on 9760 vertices, bipartite, of degree at most 5 and diameter at most 8. -/
theorem nb_5_8_n9760 : ∃ G : SimpleGraph (Fin 9760), BipartiteDD.IsBipartiteDegDiam G 5 8 := by
  have h := BipartiteDD.Haar.isBipartiteDegDiam_eight_of SS
    ((BipartiteDD.Haar.haarGraph SS).comap equiv9760.symm) equiv9760
    (fun x y => by simp [SimpleGraph.comap_adj]) coverA coverB coverC
  rw [card_SS] at h
  exact ⟨_, h⟩
