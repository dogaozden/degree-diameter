import BipartiteDD.Haar.Diam10
import BipartiteDD.Haar.PGL37Z5
import BipartiteDD.Haar.D6D10.Words

/-! The (6,10) record on 506160 vertices, as the Haar graph of `PGL(2, 37) × Z_5` with the connection set of
`research/frontier/sols/d6D10_pgl_37_5_s401.txt`. The covering hypothesis is `D6D10.cover`, proved from the
kernel-checked certificates of `D6D10.Cover` (stage modules `D6D10.Stage00 … Stage44`). -/

namespace BipartiteDD.Haar.D6D10

/-- `(PGL(2,37) × Z_5) ⊕ (PGL(2,37) × Z_5) ≃ Fin 506160`: the two sides, numbered `0 … 506159`. -/
noncomputable def equiv506160 : PGL37Z5.Grp ⊕ PGL37Z5.Grp ≃ Fin 506160 :=
  (Equiv.sumCongr PGL37Z5.equiv253080 PGL37Z5.equiv253080).trans
    (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D6D10

open BipartiteDD.Haar.D6D10 in
set_option maxHeartbeats 4000000 in
/-- A graph on 506160 vertices, bipartite, of degree at most 6 and diameter at most 10. -/
theorem nb_6_10_haar : ∃ G : SimpleGraph (Fin 506160), BipartiteDD.IsBipartiteDegDiam G 6 10 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam10_of_equiv SS equiv506160 cover
  rw [card_SS] at h
  exact ⟨_, h⟩
