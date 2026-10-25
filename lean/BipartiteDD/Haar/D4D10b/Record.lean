import BipartiteDD.Haar.D4D10b.Cover
import BipartiteDD.Haar.Diam10

/-! The (4,10) lift record on 12416 vertices, the Haar graph of `Meta97` (order 6208) with the connection set of
`research/lifts/sols/d4D10_n12416_haar_meta97_64_19.txt`. The covering hypothesis is `coverD` of `D4D10b.Cover`, and the diameter-10 lemma is
`BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`). -/

namespace BipartiteDD.Haar.D4D10b

open BipartiteDD.Haar

/-- `(Meta97 ⊕ Meta97) ≃ Fin 12416`: the two sides, numbered `0 … 12415`. -/
noncomputable def equiv12416 : Meta97.Grp ⊕ Meta97.Grp ≃ Fin 12416 :=
  (Equiv.sumCongr Meta97.equivG Meta97.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin 12416`. -/
noncomputable def G12416 : SimpleGraph (Fin 12416) := (haarGraph SS).comap equiv12416.symm

theorem isBipartiteDegDiam_G12416 : BipartiteDD.IsBipartiteDegDiam G12416 4 10 := by
  have h := haar_isBipartiteDegDiam10_of_equiv SS equiv12416 coverD
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.D4D10b

open BipartiteDD.Haar.D4D10b in
/-- A bipartite graph on 12416 vertices with degree at most 4 and diameter at most 10. -/
theorem nb_4_10_12416 : ∃ H : SimpleGraph (Fin 12416), BipartiteDD.IsBipartiteDegDiam H 4 10 :=
  ⟨G12416, isBipartiteDegDiam_G12416⟩
