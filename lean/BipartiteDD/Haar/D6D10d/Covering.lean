import BipartiteDD.Haar.D6D10d.Cover

/-! The covering hypothesis `CoverHyp SS` of the Δ6·D10 record, from the stage checks of `Cover`. -/

namespace BipartiteDD.Haar.D6D10d

theorem cover : CoverHyp SS := by
  unfold CoverHyp
  intro g
  obtain ⟨c, hc⟩ := exC (idxG g) (idxG_lt g)
  rw [gOf_idxG] at hc
  refine ⟨sG (dig c 0), sG_mem _ (dig_lt c 0), sG (dig c 1), sG_mem _ (dig_lt c 1),
    sG (dig c 2), sG_mem _ (dig_lt c 2), sG (dig c 3), sG_mem _ (dig_lt c 3),
    sG (dig c 4), sG_mem _ (dig_lt c 4), sG (dig c 5), sG_mem _ (dig_lt c 5),
    sG (dig c 6), sG_mem _ (dig_lt c 6), sG (dig c 7), sG_mem _ (dig_lt c 7),
    sG (dig c 8), sG_mem _ (dig_lt c 8), ?_⟩
  exact hc

end BipartiteDD.Haar.D6D10d
