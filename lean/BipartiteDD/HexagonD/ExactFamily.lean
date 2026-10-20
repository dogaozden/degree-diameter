import BipartiteDD.HexagonD.Exact

/-! Theorem D, slice 2, part 16 (target 4, steps 2-4, abstract form): `exact_of_family`. -/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F}

/-- If the points `X s` of the lines `m_s ∈ S_{z(s)}` through the normalised free vector `u` hit the
condition `ν(X s) = F(z(s))` for exactly one `s`, then `u` lies on exactly one line of `Wset`. -/
theorem exact_of_family (hc : ¬ IsSquare (-c)) (c0 c1 : F) {u : V7 F} (hQ : Qf u = 0)
    (hL : u 0 + c * u 4 = 1) (X : F → V7 F) (zf : F → F × F)
    (hX1 : ∀ s, X s ∈ plane u) (hX2 : ∀ s, X s 0 + c * X s 4 = 0)
    (hX3 : ∀ s, Lz c (zf s).1 (zf s).2 (X s) = 0) (hX4 : ∀ s, X s ≠ 0)
    (hzu : ∀ s, (zf s).1 * u 2 + (zf s).2 * u 5 = -1)
    (hz : ∀ a b : F, a * u 2 + b * u 5 = -1 → ∃ s, zf s = (a, b))
    (hnu : ∃! s, nuf c (X s) = Fz c c0 c1 (zf s)) :
    ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ u ∈ m.1 := by
  have hu0 : u ≠ 0 := by
    intro h
    rw [h] at hL
    simp at hL
  have hLzu : ∀ s, Lz c (zf s).1 (zf s).2 u = 0 := fun s => by
    have := hzu s
    simp only [Lz]
    linear_combination hL + this
  have hXns : ∀ s, X s ∉ span F {u} := by
    intro s h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h
    have h2 := hX2 s
    rw [← ha] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have ha0 : a = 0 := by linear_combination h2 - a * hL
    apply hX4 s
    rw [← ha, ha0, zero_smul]
  obtain ⟨s0, hs0, huniq⟩ := hnu
  have hpair : ∀ s, IsHPair u (X s) := fun s => (isHPair_iff_mem_plane hu0 hQ).2 (hX1 s)
  have hspan : ∀ s, finrank F (span F {u, X s}) = 2 := fun s => finrank_span_pair_eq_two hu0 (hXns s)
  refine ⟨hlineOf hu0 (hpair s0) (hXns s0), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- `m₀ ≠ v`
    intro h
    have hu : u ∈ (vStd : HLine F).1 := by
      rw [← h]; exact subset_span (by simp)
    have := vStd_inPi c u hu
    exact one_ne_zero (hL.symm.trans this)
  · -- `m₀ ∈ S_z`, `ν = F(z)`
    refine ⟨zf s0, ?_, ?_, X s0, subset_span (by simp), hX4 s0, hX2 s0, hs0⟩
    · intro h
      have := hzu s0
      rw [h] at this
      simp at this
    · intro x hx
      have hx' : x ∈ span F {u, X s0} := hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx'
      have h1 := hLzu s0
      have h2 := hX3 s0
      simp only [Lz, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
      linear_combination a * h1 + b * h2
  · -- `u ∈ m₀`
    exact subset_span (by simp)
  · -- uniqueness
    rintro m' ⟨⟨-, z', hz'0, hz'Pi, x', hx'm, hx'0, hx'L, hx'nu⟩, hum'⟩
    have hLz' : Lz c z'.1 z'.2 u = 0 := hz'Pi u hum'
    have hzz : z'.1 * u 2 + z'.2 * u 5 = -1 := by
      simp only [Lz] at hLz'
      linear_combination hLz' - hL
    obtain ⟨s', hs'⟩ := hz z'.1 z'.2 hzz
    have hzs' : zf s' = z' := by rw [hs']
    have hT2 := finrank_planePiZ hc z'.1 z'.2 hu0 hQ hLz'
    have hm'T : m'.1 ≤ planePiZ c z'.1 z'.2 u := hz'Pi.le_planePiZ hu0 hum'
    have hm'eq : m'.1 = planePiZ c z'.1 z'.2 u :=
      Submodule.eq_of_le_of_finrank_eq hm'T (by rw [hT2, m'.2.1])
    have hXT : X s' ∈ planePiZ c z'.1 z'.2 u :=
      mem_planePiZ.2 ⟨hX1 s', by have := hX3 s'; rwa [hzs'] at this⟩
    have huT : u ∈ planePiZ c z'.1 z'.2 u := mem_planePiZ_self hQ hLz'
    have hspanT : span F {u, X s'} = planePiZ c z'.1 z'.2 u := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (by rw [hT2, hspan])
      rw [span_le]
      intro y hy
      rcases hy with rfl | rfl
      · exact huT
      · exact hXT
    -- the vector `x'` is a multiple of `X s'`
    have hx'T : x' ∈ span F {u, X s'} := by rw [hspanT, ← hm'eq]; exact hx'm
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hx'T
    have ha0 : a = 0 := by
      have h1 := hx'L
      rw [← hab] at h1
      have h2 := hX2 s'
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1
      linear_combination h1 + a * (-hL) - b * h2
    have hb0 : b ≠ 0 := by
      rintro rfl
      apply hx'0
      rw [← hab, ha0]; simp
    have hnu' : nuf c (X s') = Fz c c0 c1 (zf s') := by
      have : x' = b • X s' := by rw [← hab, ha0]; simp
      rw [this, nuf_smul c b _ hb0] at hx'nu
      rwa [hzs']
    have hss : s' = s0 := huniq s' hnu'
    subst hss
    apply Subtype.ext
    rw [hm'eq, ← hspanT]
    rfl

end BipartiteDD.HexagonD
