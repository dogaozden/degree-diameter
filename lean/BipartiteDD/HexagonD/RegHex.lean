import BipartiteDD.HexagonD.RegLevels

/-! Theorem D, slice 2, part 23 (target 5): heights in the exact levelled hexagon.

`hgt` is the height function of the levels `lev c v W` (`W = Wset c c0 c1`, `v = ⟨e₁, e₆⟩`): vertices outside
`A₀` have height `0`, those of level `0` height `1`, `A₁ ∖ A₂` height `2`, and `v` height `3`. We record the
heights of the spread lines, their points, and the equation `h(p) + 1 = h(ℓ)` for a point `p` on a line `ℓ`
of the spread. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

/-- The height function of the levels. -/
noncomputable def hgt (c c0 c1 : F) : SPt F ⊕ HLine F → ℕ :=
  height (lev c (vStd : HLine F) (Wset c c0 c1)) (fun x => ⟨3, by simp [lev]⟩)

theorem hgt_iff (c c0 c1 : F) {i : ℕ} {x : SPt F ⊕ HLine F} :
    i < hgt c c0 c1 x ↔ x ∈ lev c (vStd : HLine F) (Wset c c0 c1) i :=
  lt_height_iff (lev_antitone (c := c) _ (vStd_inPi c) _)

theorem hgt_le (c c0 c1 : F) (x : SPt F ⊕ HLine F) : hgt c c0 c1 x ≤ 3 :=
  height_le (by simp [lev])

variable {c0 c1 : F}

/-- A line of the spread other than `v` has height `2`. -/
theorem hgt_sline {l : HLine F} (hl : InPi c l) (hlv : l ≠ vStd) : hgt c c0 c1 (Sum.inr l) = 2 := by
  have h1 : 1 < hgt c c0 c1 (Sum.inr l) := (hgt_iff c c0 c1).2 (by simpa [lev, A1] using hl)
  have h2 : ¬ 2 < hgt c c0 c1 (Sum.inr l) := fun h => by
    have := (hgt_iff c c0 c1).1 h
    simp [lev, A2] at this
    exact hlv this
  omega

/-- The line `v` has height `3`. -/
theorem hgt_v : hgt c c0 c1 (Sum.inr (vStd : HLine F)) = 3 := by
  have h1 : 2 < hgt c c0 c1 (Sum.inr (vStd : HLine F)) := (hgt_iff c c0 c1).2 (by simp [lev, A2])
  have := hgt_le c c0 c1 (Sum.inr (vStd : HLine F))
  omega

/-- A point of `Π` not on `v` has height `1`. -/
theorem hgt_pt_not_v {p : SPt F} (hp : OnPi c p) (hpv : ¬ hexInc p (vStd : HLine F)) :
    hgt c c0 c1 (Sum.inl p) = 1 := by
  have h1 : 0 < hgt c c0 c1 (Sum.inl p) := (hgt_iff c c0 c1).2 (by simpa [lev, A0] using hp)
  have h2 : ¬ 1 < hgt c c0 c1 (Sum.inl p) := fun h => by
    have := (hgt_iff c c0 c1).1 h
    simp [lev, A1] at this
    exact hpv this
  omega

/-- A point of `v` has height `2`. -/
theorem hgt_pt_v {p : SPt F} (hpv : hexInc p (vStd : HLine F)) : hgt c c0 c1 (Sum.inl p) = 2 := by
  have h1 : 1 < hgt c c0 c1 (Sum.inl p) := (hgt_iff c c0 c1).2 (by simpa [lev, A1] using hpv)
  have h2 : ¬ 2 < hgt c c0 c1 (Sum.inl p) := fun h => by
    have := (hgt_iff c c0 c1).1 h
    simp [lev, A2] at this
  omega

/-- A point on a line of the spread has height one less than the line. -/
theorem hgt_pt_on_sline (hc : ¬ IsSquare (-c)) {l : HLine F} (hl : InPi c l) {p : SPt F}
    (hp : hexInc p l) : hgt c c0 c1 (Sum.inl p) + 1 = hgt c c0 c1 (Sum.inr l) := by
  by_cases hlv : l = vStd
  · subst hlv
    rw [hgt_v, hgt_pt_v hp]
  · have hpv : ¬ hexInc p (vStd : HLine F) := fun hpv =>
      hlv (eq_of_inPi_of_mem hc hl (vStd_inPi c) hp hpv)
    rw [hgt_sline hl hlv, hgt_pt_not_v (hl _ hp) hpv]

end BipartiteDD.HexagonD
