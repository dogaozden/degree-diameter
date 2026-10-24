import BipartiteDD.Haar.D6D8d.Cover

/-! The covering hypotheses of `Diam8` for `G = PSL(2, 11) × Z24`, from the checked codes of `Cover`. -/

namespace BipartiteDD.Haar.D6D8d

open BipartiteDD.Haar.D6D8d.PSL11

theorem coverAA (g : G) : ∃ a1 ∈ SS, ∃ b1 ∈ SS, ∃ a2 ∈ SS, ∃ b2 ∈ SS, ∃ a3 ∈ SS, ∃ b3 ∈ SS,
    ∃ a4 ∈ SS, ∃ b4 ∈ SS, g = a1⁻¹ * b1 * (a2⁻¹ * b2) * (a3⁻¹ * b3) * (a4⁻¹ * b4) := by
  have h := covAA_code (idxG g) (idxG_lt g)
  have hw : gOf (idxG g) = wAA ((chunkAA (idxG g / 1584)).getD (idxG g % 1584) 0) := by
    simpa [chkAA] using h
  rw [gOf_idxG] at hw
  obtain ⟨c, hc⟩ : ∃ c, g = wAA c := ⟨_, hw⟩
  exact ⟨sG (dig c 0), sG_mem (dig_lt _ _), sG (dig c 1), sG_mem (dig_lt _ _),
    sG (dig c 2), sG_mem (dig_lt _ _), sG (dig c 3), sG_mem (dig_lt _ _),
    sG (dig c 4), sG_mem (dig_lt _ _), sG (dig c 5), sG_mem (dig_lt _ _),
    sG (dig c 6), sG_mem (dig_lt _ _), sG (dig c 6), sG_mem (dig_lt _ _), hc⟩

theorem coverBB (g : G) : ∃ a1 ∈ SS, ∃ b1 ∈ SS, ∃ a2 ∈ SS, ∃ b2 ∈ SS, ∃ a3 ∈ SS, ∃ b3 ∈ SS,
    ∃ a4 ∈ SS, ∃ b4 ∈ SS, g = a1 * b1⁻¹ * (a2 * b2⁻¹) * (a3 * b3⁻¹) * (a4 * b4⁻¹) := by
  have h := covBB_code (idxG g) (idxG_lt g)
  have hw : gOf (idxG g) = wBB ((chunkBB (idxG g / 1584)).getD (idxG g % 1584) 0) := by
    simpa [chkBB] using h
  rw [gOf_idxG] at hw
  obtain ⟨c, hc⟩ : ∃ c, g = wBB c := ⟨_, hw⟩
  exact ⟨sG (dig c 0), sG_mem (dig_lt _ _), sG (dig c 1), sG_mem (dig_lt _ _),
    sG (dig c 2), sG_mem (dig_lt _ _), sG (dig c 3), sG_mem (dig_lt _ _),
    sG (dig c 4), sG_mem (dig_lt _ _), sG (dig c 5), sG_mem (dig_lt _ _),
    sG (dig c 6), sG_mem (dig_lt _ _), sG (dig c 6), sG_mem (dig_lt _ _), hc⟩

theorem coverAB (g : G) : ∃ a ∈ SS, ∃ a1 ∈ SS, ∃ b1 ∈ SS, ∃ a2 ∈ SS, ∃ b2 ∈ SS, ∃ a3 ∈ SS, ∃ b3 ∈ SS,
    g = a * (a1⁻¹ * b1) * (a2⁻¹ * b2) * (a3⁻¹ * b3) := by
  have h := covAB_code (idxG g) (idxG_lt g)
  have hw : gOf (idxG g) = wAB ((chunkAB (idxG g / 1584)).getD (idxG g % 1584) 0) := by
    simpa [chkAB] using h
  rw [gOf_idxG] at hw
  obtain ⟨c, hc⟩ : ∃ c, g = wAB c := ⟨_, hw⟩
  exact ⟨sG (dig c 0), sG_mem (dig_lt _ _), sG (dig c 1), sG_mem (dig_lt _ _),
    sG (dig c 2), sG_mem (dig_lt _ _), sG (dig c 3), sG_mem (dig_lt _ _),
    sG (dig c 4), sG_mem (dig_lt _ _), sG (dig c 5), sG_mem (dig_lt _ _),
    sG (dig c 6), sG_mem (dig_lt _ _), hc⟩

end BipartiteDD.Haar.D6D8d
