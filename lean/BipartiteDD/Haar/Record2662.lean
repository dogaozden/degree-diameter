import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert2662

/-! The (9,5) record on 2662 vertices, as the Haar graph of the Heisenberg group mod 11 with the connection
set of `research/d5/graphs/haar_d9_n2662.json`. The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `Cert2662`. -/

namespace BipartiteDD.Haar.Heis11

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 2662`: the two sides of the Haar graph, numbered `0 … 2661`. -/
noncomputable def equiv2662 : Grp ⊕ Grp ≃ Fin 2662 :=
  haarEquiv.trans (finCongr (by rw [card_grp]))

end BipartiteDD.Haar.Heis11

open BipartiteDD.Haar.Heis11 in
/-- A graph on 2662 vertices, bipartite, of degree at most 9 and diameter at most 5. -/
theorem nb_9_5_v6 : ∃ G : SimpleGraph (Fin 2662), BipartiteDD.IsBipartiteDegDiam G 9 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv2662 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
