import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D6D7b.Cover

/-! The (6,7) record on 8440 vertices, as the Haar graph of `Z_844 ⋊ Z_5` (the `meta 844 5 477` group) with the
connection set of `research/frontier/sols/d6D7_meta_844_5_477_1_s401.txt`. The covering hypotheses are the
kernel-checked certificates of `D6D7b.Cover`, built from the stage modules `D6D7b.Stage00 … Stage04`. -/

namespace BipartiteDD.Haar.D6D7b

open BipartiteDD.Haar

/-- `(Z_844 ⋊ Z_5) ⊕ (Z_844 ⋊ Z_5) ≃ Fin 8440`: the two sides, numbered `0 … 8439`. -/
noncomputable def equiv8440 : Meta844.Grp ⊕ Meta844.Grp ≃ Fin 8440 :=
  (Equiv.sumCongr Meta844.equivG Meta844.equivG).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D7b

open BipartiteDD.Haar.D6D7b in
/-- A graph on 8440 vertices, bipartite, of degree at most 6 and diameter at most 7. -/
theorem nb_6_7_haar_8440 : ∃ G : SimpleGraph (Fin 8440), BipartiteDD.IsBipartiteDegDiam G 6 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv8440
    ⟨sel 0, sel_mem 0 (by norm_num)⟩ cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
