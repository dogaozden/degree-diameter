import BipartiteDD.Haar.Diam10
import BipartiteDD.Haar.LiftC.Words

/-! The (5,10) record on 95472 vertices, as the Haar graph of `Z_1989 ⋊ Z_24` (the `meta 1989 24 461` group) with the
connection set of `research/lifts/sols/d5D10_n95472_haar_meta1989_24_461.txt`. The covering hypothesis is `cover`
(`LiftC.Words`), built from the kernel-checked certificates of `LiftC.Cover`. -/

namespace BipartiteDD.Haar.LiftC

open BipartiteDD.Haar

/-- `(Z_1989 ⋊ Z_24) ⊕ (Z_1989 ⋊ Z_24) ≃ Fin 95472`: the two sides, numbered `0 … 95471`. -/
noncomputable def equiv95472 : Meta1989.Grp ⊕ Meta1989.Grp ≃ Fin 95472 :=
  (Equiv.sumCongr Meta1989.equivG Meta1989.equivG).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.LiftC

open BipartiteDD.Haar.LiftC in
/-- A graph on 95472 vertices, bipartite, of degree at most 5 and diameter at most 10. -/
theorem nb_5_10_95472 : ∃ G : SimpleGraph (Fin 95472), BipartiteDD.IsBipartiteDegDiam G 5 10 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv SS equiv95472 cover
  rw [card_SS] at h
  exact ⟨_, h⟩
