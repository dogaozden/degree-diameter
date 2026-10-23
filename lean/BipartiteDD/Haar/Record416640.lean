import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.D7D9.Cover

/-! The (7,9) record on 416640 vertices, as the Haar graph of `SL(2, 31) × Z_7` with the connection set of
`research/frontier/sols/d7D9_sl_31_7_s111.txt`. The covering hypotheses are the kernel-checked certificates of
`D7D9.Cover`, built from the stage modules `D7D9.Stage00 … Stage41`. -/

namespace BipartiteDD.Haar.D7D9

open BipartiteDD.Haar

/-- `(SL(2,31) × Z_7) ⊕ (SL(2,31) × Z_7) ≃ Fin 416640`: the two sides, numbered `0 … 416639`. -/
noncomputable def equiv416640 : SL31Z7.Grp ⊕ SL31Z7.Grp ≃ Fin 416640 :=
  (Equiv.sumCongr SL31Z7.equiv208320 SL31Z7.equiv208320).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D7D9

open BipartiteDD.Haar.D7D9 in
/-- A graph on 416640 vertices, bipartite, of degree at most 7 and diameter at most 9. -/
theorem nb_7_9_haar : ∃ G : SimpleGraph (Fin 416640), BipartiteDD.IsBipartiteDegDiam G 7 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS equiv416640 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
