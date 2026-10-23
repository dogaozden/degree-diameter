import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D8D7.Cover

/-! The (8,7) record on 41040 vertices, as the Haar graph of `SL(2, 19) × Z_3` with the connection set of
`research/frontier/sols/d8D7_sl_19_3_s2.txt`. The covering hypotheses are the kernel-checked certificates of
`D8D7.Cover`, built from the stage modules `D8D7.Stage00 … Stage11`. -/

namespace BipartiteDD.Haar.D8D7

open BipartiteDD.Haar

/-- `(SL(2,19) × Z_3) ⊕ (SL(2,19) × Z_3) ≃ Fin 41040`: the two sides, numbered `0 … 41039`. -/
noncomputable def equiv41040 : SL19Z3.Grp ⊕ SL19Z3.Grp ≃ Fin 41040 :=
  (Equiv.sumCongr SL19Z3.equiv20520 SL19Z3.equiv20520).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D8D7

open BipartiteDD.Haar.D8D7 in
/-- A graph on 41040 vertices, bipartite, of degree 8 and diameter at most 7. -/
theorem nb_8_7_haar : ∃ G : SimpleGraph (Fin 41040), BipartiteDD.IsBipartiteDegDiam G 8 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv41040 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
