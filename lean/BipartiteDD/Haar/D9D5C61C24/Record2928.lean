import BipartiteDD.Haar.Main
import BipartiteDD.Haar.D9D5C61C24.Cert

/-! The (9,5) record on 2928 vertices, as the Haar graph of `G = C61 : C24` (y acts with order 6) with the connection set
`S` of `research/selfdual-d5/records/d9D5_n2928_haar_c61c24.edges`. The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `D9D5C61C24.Cert`. -/

namespace BipartiteDD.Haar.D9D5C61C24

/-- `Grp ⊕ Grp ≃ Fin 2928`: the two sides of the Haar graph, numbered `0 … 2927`. -/
def equiv2928 : Grp ⊕ Grp ≃ Fin 2928 :=
  (Equiv.sumCongr equiv1464 equiv1464).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D9D5C61C24

open BipartiteDD.Haar.D9D5C61C24 in
/-- A graph on 2928 vertices, bipartite, of degree at most 9 and diameter at most 5. -/
theorem nb_9_5_n2928 : ∃ G : SimpleGraph (Fin 2928), BipartiteDD.IsBipartiteDegDiam G 9 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv2928 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
