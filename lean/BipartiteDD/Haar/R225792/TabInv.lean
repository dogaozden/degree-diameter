import BipartiteDD.Haar.R225792.TabDefs

namespace BipartiteDD.Haar.R225792

open M2

theorem iP_ok : ∀ i < 168, iPcheck i = true := by
  decide +kernel

theorem iQ_ok : ∀ j < 336, iQcheck j = true := by
  decide +kernel

end BipartiteDD.Haar.R225792
