import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D5D7b.Cover

/-! The (5,7) record on 3120 vertices, as the Haar graph of `PGL(2, 5) × Z_13` with the connection set of
`research/lifts/sols/haar/hc_d5D7_pgl_5_13_s1.txt`. The covering hypotheses are the kernel-checked certificates of
`D5D7b.Cover`, built from the stage modules `D5D7b.Stage00 … Stage05`. -/

namespace BipartiteDD.Haar.D5D7b

open BipartiteDD.Haar

/-- `(PGL(2, 5) × Z_13) ⊕ (PGL(2, 5) × Z_13) ≃ Fin 3120`: the two sides, numbered `0 … 3119`. -/
noncomputable def equiv3120 : PGL5Z13.Grp ⊕ PGL5Z13.Grp ≃ Fin 3120 :=
  (Equiv.sumCongr PGL5Z13.equiv1560 PGL5Z13.equiv1560).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D5D7b

open BipartiteDD.Haar.D5D7b in
/-- A graph on 3120 vertices, bipartite, of degree at most 5 and diameter at most 7. -/
theorem nb_5_7_3120 : ∃ G : SimpleGraph (Fin 3120), BipartiteDD.IsBipartiteDegDiam G 5 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv3120 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
