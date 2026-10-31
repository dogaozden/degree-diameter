import BipartiteDD.Haar.Diam7
import BipartiteDD.Haar.D4D7Heis9C16.Cover

/-! The (4,7) record on 864 vertices: the Haar graph of `G = Heis(F_9) ⋊ C_16` (order 432, `SmallGroup(432,233)`) with the
connection set `S` of `research/theorems/smallfam/graphs/d4D7_n864_heis9xC16.edges.gz`. The covering hypotheses are the
kernel-checked certificates of `D4D7Heis9C16.Cover`. -/

namespace BipartiteDD.Haar.D4D7Heis9C16

/-- `(Heis(F_9) ⋊ C_16) ⊕ (Heis(F_9) ⋊ C_16) ≃ Fin 864`: the two sides, numbered `0 … 863`. -/
def equiv864 : Grp ⊕ Grp ≃ Fin 864 :=
  (Equiv.sumCongr equiv432 equiv432).trans (finSumFinEquiv.trans (finCongr (by norm_num)))

end BipartiteDD.Haar.D4D7Heis9C16

open BipartiteDD.Haar.D4D7Heis9C16 in
/-- A graph on 864 vertices, bipartite, of degree at most 4 and diameter at most 7. -/
theorem nb_4_7_864 : ∃ G : SimpleGraph (Fin 864), BipartiteDD.IsBipartiteDegDiam G 4 7 := by
  have h := BipartiteDD.Haar.haar_isBipartiteDegDiam7_of_equiv SS equiv864 ⟨s0, by decide⟩ cover1 cover2
  rw [card_SS] at h
  exact ⟨_, h⟩
