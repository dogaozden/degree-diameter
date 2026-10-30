import BipartiteDD.Haar.Main
import BipartiteDD.Haar.D7D5SL5.Cert

/-! The (7,5) record on 1200 vertices, as the Haar graph of `SL(2, 5) × Z_5` with the connection set of
`research/beyond-haar-d5/records/d7D5_n1200_haar_sl5xc5.txt`. The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `D7D5SL5.Cert`. -/

namespace BipartiteDD.Haar.D7D5SL5

/-- `Grp ⊕ Grp ≃ Fin 1200`: the two sides of the Haar graph, numbered `0 … 1199`. -/
def equiv1200 : Grp ⊕ Grp ≃ Fin 1200 :=
  (Equiv.sumCongr equiv600 equiv600).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D5SL5

open BipartiteDD.Haar.D7D5SL5 in
/-- A graph on 1200 vertices, bipartite, of degree at most 7 and diameter at most 5. -/
theorem nb_7_5_n1200 : ∃ G : SimpleGraph (Fin 1200), BipartiteDD.IsBipartiteDegDiam G 7 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv1200 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
