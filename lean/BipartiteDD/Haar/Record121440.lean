import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.D6D9.Cover

/-! The (6,9) record on 121440 vertices, as the Haar graph of `SL(2, 23) × Z_5` with the connection set of
`research/frontier/sols/d6D9_sl_23_5_s401.txt`. The covering hypotheses are the kernel-checked certificates of
`D6D9.Cover`, built from the stage modules `D6D9.Stage00 … Stage11`. -/

namespace BipartiteDD.Haar.D6D9

open BipartiteDD.Haar

/-- `(SL(2,23) × Z_5) ⊕ (SL(2,23) × Z_5) ≃ Fin 121440`: the two sides, numbered `0 … 121439`. -/
noncomputable def equiv121440 : SL23Z5.Grp ⊕ SL23Z5.Grp ≃ Fin 121440 :=
  (Equiv.sumCongr SL23Z5.equiv60720 SL23Z5.equiv60720).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D9

open BipartiteDD.Haar.D6D9 in
/-- A graph on 121440 vertices, bipartite, of degree at most 6 and diameter at most 9. -/
theorem nb_6_9_haar : ∃ G : SimpleGraph (Fin 121440), BipartiteDD.IsBipartiteDegDiam G 6 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS equiv121440 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
