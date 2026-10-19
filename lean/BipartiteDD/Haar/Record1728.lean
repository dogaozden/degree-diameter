import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert1728

/-! The (8,5) record on 1728 vertices, as the Haar graph of `Z_144 ⋊ Z_6` with the connection set of
`records/bipartite_dd/d8D5/1728-d5-haar_d8_n1728.json`. The covering hypotheses are the kernel-checked
certificates of `Cert1728`. -/

namespace BipartiteDD.Haar.Z144

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 1728`: the two sides of the Haar graph, numbered `0 … 1727`. -/
noncomputable def equiv1728 : Grp ⊕ Grp ≃ Fin 1728 :=
  haarEquiv.trans (finCongr (by rw [card_grp]))

end BipartiteDD.Haar.Z144

open BipartiteDD.Haar.Z144 in
/-- A graph on 1728 vertices, bipartite, of degree at most 8 and diameter at most 5. -/
theorem nb_8_5_haar : ∃ G : SimpleGraph (Fin 1728), BipartiteDD.IsBipartiteDegDiam G 8 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv S8 equiv1728 ⟨s8 0, s8_mem 0⟩ cover1 cover2
  rw [card_S8] at h
  exact ⟨_, h⟩
