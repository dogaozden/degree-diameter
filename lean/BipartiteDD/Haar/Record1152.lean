import BipartiteDD.Haar.Main
import BipartiteDD.Haar.Cert1152

/-! The (7,5) record on 1152 vertices, as the Haar graph of `S_4 × Z_24`
(`Equiv.Perm (Fin 4) × Multiplicative (ZMod 24)`) with the connection set of `docs/lean-1152-brief.md`.
The covering hypotheses of the Haar lemma are the kernel-checked certificates of `Cert1152`. -/

namespace BipartiteDD.Haar.S4Z24

open BipartiteDD.Haar

/-- `Grp ⊕ Grp ≃ Fin 1152`: the two sides of the Haar graph, numbered `0 … 1151`. -/
noncomputable def equiv1152 : Grp ⊕ Grp ≃ Fin 1152 :=
  haarEquiv.trans (finCongr (by rw [card_grp]))

end BipartiteDD.Haar.S4Z24

open BipartiteDD.Haar.S4Z24 in
/-- A graph on 1152 vertices, bipartite, of degree at most 7 and diameter at most 5. -/
theorem nb_7_5_v2 : ∃ G : SimpleGraph (Fin 1152), BipartiteDD.IsBipartiteDegDiam G 7 5 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam_of_equiv SS equiv1152 ⟨sS 0, sS_mem 0⟩
    cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
