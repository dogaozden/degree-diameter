import BipartiteDD.Haar.LiftA.D4D10.Cover
import BipartiteDD.Haar.Diam10

/-! The (4,10) lift record on 12246 vertices, the Haar graph of `Meta157` (order 6123) with the connection set of
`research/lifts/sols/d4D10_n12246_haar_meta157_39_9.txt`. The covering hypothesis is `coverD` of `D4D10.Cover`, and the diameter-10 lemma is
`BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv` (`Haar/Diam10.lean`). -/

namespace BipartiteDD.Haar.LiftA.D4D10

open BipartiteDD.Haar

/-- `(Meta157 ⊕ Meta157) ≃ Fin 12246`: the two sides, numbered `0 … 12245`. -/
noncomputable def equiv12246 : Meta157.Grp ⊕ Meta157.Grp ≃ Fin 12246 :=
  (Equiv.sumCongr Meta157.equivG Meta157.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin 12246`. -/
def G12246 : SimpleGraph (Fin 12246) := (haarGraph SS).comap equiv12246.symm

theorem isBipartiteDegDiam_G12246 : BipartiteDD.IsBipartiteDegDiam G12246 4 10 := by
  have h := haar_isBipartiteDegDiam10_of_equiv SS equiv12246 coverD
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.LiftA.D4D10

open BipartiteDD.Haar.LiftA.D4D10 in
/-- A bipartite graph on 12246 vertices with degree at most 4 and diameter at most 10. -/
theorem nb_4_10_12246 : ∃ H : SimpleGraph (Fin 12246), BipartiteDD.IsBipartiteDegDiam H 4 10 :=
  ⟨G12246, isBipartiteDegDiam_G12246⟩
