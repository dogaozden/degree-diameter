import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert2640

/-! The (9,5) record on 2640 vertices, as the Haar graph of `SL(2, 11)` with connection set `SS`
(`research/d5/graphs/haar_d9_n2640_sl2_11.json`). The covering hypotheses of the Haar lemma are the
kernel-checked certificates of `Cert2640`. -/

namespace BipartiteDD.Haar.SL211

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 2640`: the two sides of the Haar graph, numbered `0 … 2639`. -/
noncomputable def equiv2640 : Grp ⊕ Grp ≃ Fin 2640 :=
  (Equiv.sumCongr equiv1320 equiv1320).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.SL211

open BipartiteDD.Haar.SL211 in
/-- A graph on 2640 vertices, bipartite, of degree at most 9 and diameter at most 5. -/
theorem nb_9_5_v5 : ∃ G : SimpleGraph (Fin 2640), BipartiteDD.IsBipartiteDegDiam G 9 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv2640 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
