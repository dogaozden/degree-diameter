import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.LiftB.Cover

/-! The (5,9) record on 28560 vertices, as the Haar graph of `Z_595 ⋊ Z_24` with the connection set of
`research/lifts/sols/d5D9_n28560_haar_meta595_24_53.txt`. The covering hypotheses are the kernel-checked certificates of
`LiftB.Cover`, built from the stage modules `LiftB.Stage00 … Stage09`. -/

namespace BipartiteDD.Haar.LiftB

open BipartiteDD.Haar

/-- `(Z_595 ⋊ Z_24) ⊕ (Z_595 ⋊ Z_24) ≃ Fin 28560`: the two sides, numbered `0 … 28559`. -/
noncomputable def equiv28560 : Meta595.Grp ⊕ Meta595.Grp ≃ Fin 28560 :=
  (Equiv.sumCongr Meta595.equivG Meta595.equivG).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.LiftB

open BipartiteDD.Haar.LiftB in
/-- A graph on 28560 vertices, bipartite, of degree at most 5 and diameter at most 9. -/
theorem nb_5_9_28560 : ∃ G : SimpleGraph (Fin 28560), BipartiteDD.IsBipartiteDegDiam G 5 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS equiv28560
    ⟨sel 0, sel_mem 0 (by norm_num)⟩ cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
