import BipartiteDD.Haar.Main
import BipartiteDD.Haar.D9D5C69C22.Cert

/-! The (9,5) record on 3036 vertices, as the Haar graph of `G = C69 : C22` (y acts with order 22) with the connection set
`S` of `research/selfdual-d5/records/d9D5_n3036_haar_c69c22.edges`. The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `D9D5C69C22.Cert`. -/

namespace BipartiteDD.Haar.D9D5C69C22

/-- `Grp ⊕ Grp ≃ Fin 3036`: the two sides of the Haar graph, numbered `0 … 3035`. -/
def equiv3036 : Grp ⊕ Grp ≃ Fin 3036 :=
  (Equiv.sumCongr equiv1518 equiv1518).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D9D5C69C22

open BipartiteDD.Haar.D9D5C69C22 in
/-- A graph on 3036 vertices, bipartite, of degree at most 9 and diameter at most 5. -/
theorem nb_9_5_n3036 : ∃ G : SimpleGraph (Fin 3036), BipartiteDD.IsBipartiteDegDiam G 9 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv3036 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
