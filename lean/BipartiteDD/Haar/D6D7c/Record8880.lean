import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D6D7c.Cover

/-! The (6,7) record on 8880 vertices, as the Haar graph of `SL(2, 5) × Z_37` with the connection set of
`research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt`. The covering hypotheses are the kernel-checked certificates of
`D6D7c.Cover`, built from the stage modules `D6D7c.Stage00 … Stage04`. -/

namespace BipartiteDD.Haar.D6D7c

open BipartiteDD.Haar

/-- `(SL(2,5) × Z_37) ⊕ (SL(2,5) × Z_37) ≃ Fin 8880`: the two sides, numbered `0 … 8879`. -/
noncomputable def equiv8880 : SL5Z37.Grp ⊕ SL5Z37.Grp ≃ Fin 8880 :=
  (Equiv.sumCongr SL5Z37.equiv4440 SL5Z37.equiv4440).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D7c

open BipartiteDD.Haar.D6D7c in
/-- A graph on 8880 vertices, bipartite, of degree at most 6 and diameter at most 7. -/
theorem nb_6_7_8880 : ∃ G : SimpleGraph (Fin 8880), BipartiteDD.IsBipartiteDegDiam G 6 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv8880
    ⟨sel 0, sel_mem 0 (by norm_num)⟩ cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
