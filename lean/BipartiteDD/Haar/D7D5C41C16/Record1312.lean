import BipartiteDD.Haar.Main
import BipartiteDD.Haar.D7D5C41C16.Cert

/-! The (7,5) record on 1312 vertices, as the Haar graph of `G = C41 : C16` (SmallGroup(656,28)) with the connection set
`S` of `research/d75-raise/records/d7D5_n1312_haar_c41c16.edges`. The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `D7D5C41C16.Cert`. -/

namespace BipartiteDD.Haar.D7D5C41C16

/-- `Grp ⊕ Grp ≃ Fin 1312`: the two sides of the Haar graph, numbered `0 … 1311`. -/
def equiv1312 : Grp ⊕ Grp ≃ Fin 1312 :=
  (Equiv.sumCongr equiv656 equiv656).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D5C41C16

open BipartiteDD.Haar.D7D5C41C16 in
/-- A graph on 1312 vertices, bipartite, of degree at most 7 and diameter at most 5. -/
theorem nb_7_5_n1312 : ∃ G : SimpleGraph (Fin 1312), BipartiteDD.IsBipartiteDegDiam G 7 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv1312 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
