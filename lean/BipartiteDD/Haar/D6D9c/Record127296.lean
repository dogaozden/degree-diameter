import BipartiteDD.Haar.Diam9
import BipartiteDD.Haar.D6D9c.Cover

/-! The (6,9) record on 127296 vertices, as the Haar graph of `SL(2, 17) × Z_13` with the connection set of
`research/frontier/sols/d6D9_sl_17_13_orb3f0_s2.txt`. The covering hypotheses are the kernel-checked certificates of
`D6D9c.Cover`, built from the stage modules `D6D9c.Stage00 … Stage12`. -/

namespace BipartiteDD.Haar.D6D9c

open BipartiteDD.Haar

/-- `(SL(2,17) × Z_13) ⊕ (SL(2,17) × Z_13) ≃ Fin 127296`: the two sides, numbered `0 … 127295`. -/
noncomputable def equiv127296 : SL17Z13.Grp ⊕ SL17Z13.Grp ≃ Fin 127296 :=
  (Equiv.sumCongr SL17Z13.equiv63648 SL17Z13.equiv63648).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D9c

open BipartiteDD.Haar.D6D9c in
/-- A graph on 127296 vertices, bipartite, of degree at most 6 and diameter at most 9. -/
theorem nb_6_9_127296 : ∃ G : SimpleGraph (Fin 127296), BipartiteDD.IsBipartiteDegDiam G 6 9 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam9_of_equiv SS equiv127296 ⟨sel 0, sel_mem 0 (by norm_num)⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
