import BipartiteDD.HexagonD.ExactCharts

/-! Theorem D, slice 2, part 18 (target 4): free points and the whisker set.

* `exists_line_meets_vStd`: a nonzero singular vector with `x₂ = x₅ = 0` is collinear with a point of `v`
  (so a free point has `(x₂, x₅) ≠ 0`, the point of step 2 of the report);
* `exists_unique_wline`: every free point lies on exactly one line of `Wset` (step 4);
* `wset_whiskers`: `Wset` satisfies the whisker hypotheses (lines opposite `v`, not in `S`, no free point on
  two of them). -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

/-- A nonzero singular vector with `x₂ = x₅ = 0` is on a line meeting `v`. -/
theorem exists_line_meets_vStd {x : V7 F} (hx0 : x ≠ 0) (hQ : Qf x = 0) (h2 : x 2 = 0) (h5 : x 5 = 0) :
    ∃ M : HLine F, x ∈ M.1 ∧ ∃ r : SPt F, hexInc r (vStd : HLine F) ∧ hexInc r M := by
  -- the point `r' = (0, a, 0, 0, 0, 0, b)` of `v`
  obtain ⟨a, b, hab, hc1, hc2⟩ : ∃ a b : F, (a ≠ 0 ∨ b ≠ 0) ∧ a * x 0 = b * x 3 ∧ b * x 4 = a * x 3 := by
    by_cases h : x 3 = 0 ∧ x 0 = 0
    · exact ⟨1, 0, Or.inl one_ne_zero, by simp [h.2], by simp [h.1]⟩
    · refine ⟨x 3, x 0, ?_, by ring, ?_⟩
      · by_contra hh
        push Not at hh
        exact h hh
      · simp only [Qf] at hQ
        rw [h2, h5] at hQ
        linear_combination hQ
  let r' : V7 F := ![0, a, 0, 0, 0, 0, b]
  have hr'0 : r' ≠ 0 := by
    intro h
    have h1 := congr_fun h 1
    have h6 := congr_fun h 6
    simp [r'] at h1 h6
    rcases hab with h | h
    · exact h h1
    · exact h h6
  have hr'Q : Qf r' = 0 := by simp [Qf, r']
  have hr'v : r' ∈ (vStd : HLine F).1 := mem_vStd.2 (by simp [r'])
  have hpair : IsHPair x r' := by
    refine ⟨hQ, hr'Q, ?_, ?_⟩
    · simp [Bf, r', h2, h5]
    · simp only [Tits, pl, r']
      simp [h2, h5]
      refine ⟨?_, ?_⟩
      · linear_combination hc1
      · linear_combination hc2
  obtain ⟨M, hxM, hr'M⟩ := exists_hline_of_isHPair hx0 hpair
  exact ⟨M, hxM, sptOf r' hr'0 hr'Q, sptOf_mem.2 hr'v, sptOf_mem.2 hr'M⟩

/-- Scaling: membership of a projective point in a line. -/
theorem smul_rep_mem {p : SPt F} {m : HLine F} {a : F} (ha : a ≠ 0) :
    a • p.1.rep ∈ m.1 ↔ hexInc p m := by
  constructor
  · intro h
    have := m.1.smul_mem a⁻¹ h
    show p.1.rep ∈ m.1
    simpa [smul_smul, inv_mul_cancel₀ ha] using this
  · intro h
    exact m.1.smul_mem a h

/-- **Step 4**: every free point lies on exactly one line of `Wset`. -/
theorem exists_unique_wline (hc : ¬ IsSquare (-c)) {c0 c1 : F} (hG : GoodCubic c c0 c1) {p : SPt F}
    (hp : ¬ OnPi c p) (hfree : ¬ ∃ M : HLine F, hexInc p M ∧ Meets (vStd : HLine F) M) :
    ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ hexInc p m := by
  have hL : p.1.rep 0 + c * p.1.rep 4 ≠ 0 := hp
  set ℓ := p.1.rep 0 + c * p.1.rep 4 with hℓ
  set u : V7 F := ℓ⁻¹ • p.1.rep with hu
  have hQ : Qf u = 0 := by rw [hu, Qf_smul, p.2, mul_zero]
  have hLu : u 0 + c * u 4 = 1 := by
    simp only [hu, Pi.smul_apply, smul_eq_mul]
    field_simp
    exact hℓ.symm
  have hmem : ∀ m : HLine F, u ∈ m.1 ↔ hexInc p m := fun m => smul_rep_mem (inv_ne_zero hL)
  have hu0 : u ≠ 0 := by intro h; rw [h] at hLu; simp at hLu
  have h25 : ¬ (u 2 = 0 ∧ u 5 = 0) := by
    rintro ⟨h2, h5⟩
    obtain ⟨M, hxM, hM⟩ := exists_line_meets_vStd hu0 hQ h2 h5
    exact hfree ⟨M, (hmem M).1 hxM, hM⟩
  have key : ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ u ∈ m.1 := by
    by_cases h5 : u 5 = 0
    · have h2 : u 2 ≠ 0 := fun h2 => h25 ⟨h2, h5⟩
      exact exact_chartB hc hG hQ hLu h5 h2
    · exact exact_chartA hc hG hQ hLu h5
  simpa only [hmem] using key

/-- `Wset` is a set of whiskers for the spread line `v = ⟨e₁, e₆⟩`. -/
theorem wset_whiskers (hc : ¬ IsSquare (-c)) {c0 c1 : F} (hG : GoodCubic c c0 c1) :
    Whiskers c (vS c) (Wset c c0 c1) where
  not_inPi w hw hwPi := by
    obtain ⟨hne, z, hz0, hzPi, -⟩ := hw
    exact hne (no_second_line hc hz0 hzPi hwPi)
  opp w hw := by
    obtain ⟨hne, z, hz0, hzPi, -⟩ := hw
    exact slineZ_opp hc z.1 z.2 (vStd_Lz c z.1 z.2) hzPi (Ne.symm hne)
  free p hp hfree w hw w' hw' hpw hpw' := by
    obtain ⟨m, -, huniq⟩ := exists_unique_wline hc hG hp hfree
    exact (huniq w ⟨hw, hpw⟩).trans (huniq w' ⟨hw', hpw'⟩).symm

end BipartiteDD.HexagonD
