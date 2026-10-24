import BipartiteDD.Haar.D9D8c.Cover
import BipartiteDD.Haar.GraphD

/-! The covering hypothesis of `isBipartiteDegDiam8_even_of` for `G = PSL(2, 19) × Z79`, from the checked codes of
`Cover`: every `x` is `s * (p₁⁻¹ p₂) (p₃⁻¹ p₄) (p₅⁻¹ p₆)` with `s, p₁, …, p₆ ∈ SS`. -/

namespace BipartiteDD.Haar.D9D8c

open BipartiteDD.Haar

theorem coverE (x : G) : ∃ s ∈ SS, IsLeftWord SS 3 (s⁻¹ * x) := by
  obtain ⟨c, hc⟩ := exE (idxG x) (idxG_lt x)
  have h : gOf (idxG x) = wE c := of_decide_eq_true hc
  rw [gOf_idxG] at h
  subst h
  refine ⟨sG (dig c 0), sG_mem (dig_lt _ _), ?_⟩
  refine ⟨[(sG (dig c 1), sG (dig c 2)), (sG (dig c 3), sG (dig c 4)), (sG (dig c 5), sG (dig c 6))],
    by simp, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨sG_mem (dig_lt _ _), sG_mem (dig_lt _ _)⟩
  · simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, wE]
    group

end BipartiteDD.Haar.D9D8c
