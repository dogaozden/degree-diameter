import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.D5D9N29756.Cover

/-! The (5,9) record on 29756 vertices, as the Haar graph of `G = C346 : C43` (y acts with order 43) with the connection
set `S` of `research/frontier/sols/d5D9_meta_346_43_29_s613_n29756.txt`. The covering hypotheses of the diameter-9 lemma
`Diam9.lean` are the kernel-checked chunks of `D5D9N29756.Cover`. -/

namespace BipartiteDD.Haar.D5D9N29756

/-- `Grp ⊕ Grp ≃ Fin 29756`: the two sides of the Haar graph, numbered `0 … 29755`. -/
def equiv29756 : Grp ⊕ Grp ≃ Fin 29756 :=
  (Equiv.sumCongr equiv14878 equiv14878).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D5D9N29756

open BipartiteDD.Haar.D5D9N29756 in
/-- A graph on 29756 vertices, bipartite, of degree at most 5 and diameter at most 9. -/
theorem nb_5_9_n29756 : ∃ G : SimpleGraph (Fin 29756), BipartiteDD.IsBipartiteDegDiam G 5 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS equiv29756 ⟨sS 0, sS_mem 0⟩ coverA coverB
  rw [card_SS] at h
  exact ⟨_, h⟩
