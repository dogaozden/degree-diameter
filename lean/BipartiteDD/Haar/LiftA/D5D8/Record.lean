import BipartiteDD.Haar.LiftA.D5D8.Cover
import BipartiteDD.Haar.Diam8

/-! The (5,8) lift record on 9576 vertices, the Haar graph of `Meta266` (order 4788) with the connection set of
`research/lifts/sols/d5D8_n9576_haar_meta266_18_17.txt`. The covering hypotheses are `coverA`, `coverB`, `coverC` of `D5D8.Cover`, and the
diameter-8 lemma is `BipartiteDD.Haar.isBipartiteDegDiam8_of` (`Haar/Diam8.lean`). -/

namespace BipartiteDD.Haar.LiftA.D5D8

open BipartiteDD.Haar

/-- `(Meta266 ⊕ Meta266) ≃ Fin 9576`: the two sides, numbered `0 … 9575`. -/
noncomputable def equiv9576 : Meta266.Grp ⊕ Meta266.Grp ≃ Fin 9576 :=
  (Equiv.sumCongr Meta266.equivG Meta266.equivG).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

/-- The Haar graph of `SS`, transported to `Fin 9576`. -/
def G9576 : SimpleGraph (Fin 9576) := (haarGraph SS).comap equiv9576.symm

theorem isBipartiteDegDiam_G9576 : BipartiteDD.IsBipartiteDegDiam G9576 5 8 := by
  have h := isBipartiteDegDiam8_of SS G9576 equiv9576 (fun x y => by simp [G9576, SimpleGraph.comap_adj])
    coverA coverB coverC
  rw [card_SS] at h
  exact h

end BipartiteDD.Haar.LiftA.D5D8

open BipartiteDD.Haar.LiftA.D5D8 in
/-- A bipartite graph on 9576 vertices with degree at most 5 and diameter at most 8. -/
theorem nb_5_8_9576 : ∃ H : SimpleGraph (Fin 9576), BipartiteDD.IsBipartiteDegDiam H 5 8 :=
  ⟨G9576, isBipartiteDegDiam_G9576⟩
