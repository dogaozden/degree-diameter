import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D8D7b.Cover

/-! The (8,7) record on 43344 vertices, as the Haar graph of `SL(2, 8) × Z_43` with the connection set of
`research/frontier/sols/d8D7_sl_8_43_orb3_s1.txt`. The covering hypotheses are the kernel-checked certificates of
`D8D7b.Cover`, built from the stage modules `D8D7b.Stage00 … Stage11`. -/

namespace BipartiteDD.Haar.D8D7b

open BipartiteDD.Haar

/-- `(SL(2,8) × Z_43) ⊕ (SL(2,8) × Z_43) ≃ Fin 43344`: the two sides, numbered `0 … 43343`. -/
noncomputable def equiv43344 : SL8Z43.Grp ⊕ SL8Z43.Grp ≃ Fin 43344 :=
  (Equiv.sumCongr SL8Z43.equiv21672 SL8Z43.equiv21672).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D8D7b

open BipartiteDD.Haar.D8D7b in
/-- A graph on 43344 vertices, bipartite, of degree 8 and diameter at most 7. -/
theorem nb_8_7_43344 : ∃ G : SimpleGraph (Fin 43344), BipartiteDD.IsBipartiteDegDiam G 8 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv43344 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
