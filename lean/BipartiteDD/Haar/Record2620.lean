import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert2620

/-! The (9,5) record on 2620 vertices, as the Haar graph of `Z_131 ⋊ Z_10` with connection set `S`
(`research/d5/sols/h2_d9_N1310_m131_k10_l53.txt`). The covering hypotheses of the Haar lemma are
the kernel-checked certificates of `Cert2620`. -/

namespace BipartiteDD.Haar.Z131

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 2620`: the two sides of the Haar graph, numbered `0 … 2619`. -/
noncomputable def equiv2620 : Grp ⊕ Grp ≃ Fin 2620 :=
  haarEquiv.trans (finCongr (by rw [card_grp]))

end BipartiteDD.Haar.Z131

open BipartiteDD.Haar.Z131 in
/-- A graph on 2620 vertices, bipartite, of degree at most 9 and diameter at most 5. -/
theorem nb_9_5_v3 : ∃ G : SimpleGraph (Fin 2620), BipartiteDD.IsBipartiteDegDiam G 9 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv S9 equiv2620 ⟨s9 0, s9_mem 0⟩ cover1 cover2
  rw [card_S9] at h
  exact ⟨_, h⟩
