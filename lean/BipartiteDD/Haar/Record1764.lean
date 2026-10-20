import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert1764

/-! The (8,5) record on 1764 vertices, as the Haar graph of `AGL(1,7) × Z_21` with the connection set of
`research/d5/graphs/haar_d8_n1764.json` (written in the coordinates of `AGL17Z21`). The covering
hypotheses of the Haar lemma are the kernel-checked certificates of `Cert1764`. -/

namespace BipartiteDD.Haar.AGL17Z21

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 1764`: the two sides of the Haar graph, numbered `0 … 1763`. -/
noncomputable def equiv1764 : Grp ⊕ Grp ≃ Fin 1764 :=
  haarEquiv.trans (finCongr (by rw [card_grp]))

end BipartiteDD.Haar.AGL17Z21

open BipartiteDD.Haar.AGL17Z21 in
/-- A graph on 1764 vertices, bipartite, of degree at most 8 and diameter at most 5. -/
theorem nb_8_5_v2 : ∃ G : SimpleGraph (Fin 1764), BipartiteDD.IsBipartiteDegDiam G 8 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv1764 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
