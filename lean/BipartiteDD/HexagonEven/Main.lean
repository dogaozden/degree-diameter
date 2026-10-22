import BipartiteDD.HexagonEven.Through
import BipartiteDD.Hexagon.Main

/-! Split Cayley hexagon `H(q)` for every finite field, part 3: the incidence graph is a generalized hexagon.

The proof of `BipartiteDD.Hexagon.genPolygonGraph_hexagon` (odd `q`) with `finrank_plane_all` in place of
`finrank_plane`, so the hypothesis `NeZero (2 : F)` disappears. Characteristic-free helpers (`hexInc`, `zvec`,
`phi_zvec`, `sptOf`, `sptOf_mem`) are reused from `BipartiteDD.Hexagon.Main`. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule
open scoped Classical

variable {F : Type*} [Field F]

theorem exists_hline_through_even {x : V7 F} (hx : x ≠ 0) (hQ : Qf x = 0) :
    ∃ M : HLine F, x ∈ M.1 := by
  have hnot : ¬ plane x ≤ span F {x} := by
    intro h
    have := Submodule.finrank_mono h
    rw [finrank_plane_all hx hQ, finrank_span_singleton hx] at this
    omega
  obtain ⟨y, hy, hy'⟩ := SetLike.not_le_iff_exists.1 hnot
  exact ⟨hlineOf hx ((isHPair_iff_mem_plane hx hQ).2 hy) hy', subset_span (by simp)⟩

theorem exists_hline_of_isHPair_even {a b : V7 F} (ha : a ≠ 0) (h : IsHPair a b) :
    ∃ M : HLine F, a ∈ M.1 ∧ b ∈ M.1 := by
  by_cases hb : b ∈ span F {a}
  · obtain ⟨M, hM⟩ := exists_hline_through_even ha h.1
    refine ⟨M, hM, ?_⟩
    have : span F {a} ≤ M.1 := span_le.2 (by simpa using hM)
    exact this hb
  · exact ⟨hlineOf ha h hb, subset_span (by simp), subset_span (by simp)⟩

/-- Every line has a nonzero vector orthogonal to a given vector. -/
theorem exists_orth_even (x : V7 F) (W : HLine F) : ∃ w ∈ W.1, w ≠ 0 ∧ Bf x w = 0 := by
  let f : W.1 →ₗ[F] F := (BfForm F x).comp W.1.subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 2 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [W.2.1] at this
    exact this
  have h2 : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 0 < finrank F (LinearMap.ker f) := by omega
  have hne : LinearMap.ker f ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at h3
    exact lt_irrefl _ h3
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨v.1, v.2, fun h => hv0 ?_, ?_⟩
  · apply Subtype.ext; exact h
  · simpa [f, LinearMap.mem_ker] using hv

theorem exists_mid_even {x w : V7 F} (hx : x ≠ 0) (hxQ : Qf x = 0) (hw : w ≠ 0) (hwQ : Qf w = 0)
    (hB : Bf x w = 0) :
    ∃ m : SPt F, (∃ M : HLine F, x ∈ M.1 ∧ m.1.rep ∈ M.1) ∧ (∃ M : HLine F, m.1.rep ∈ M.1 ∧ w ∈ M.1) := by
  have hz := phi_zvec hB
  by_cases hz0 : zvec x w = 0
  · rw [hz0, phi_zero] at hz
    have hxw : IsHPair x w := isHPair_iff.2 ⟨hxQ, hwQ, hz.symm⟩
    refine ⟨sptOf x hx hxQ, ?_, ?_⟩
    · obtain ⟨M, hM⟩ := exists_hline_through_even hx hxQ
      exact ⟨M, hM, sptOf_mem.2 hM⟩
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair_even hx hxw
      exact ⟨M, sptOf_mem.2 h1, h2⟩
  · have hzQ : Qf (zvec x w) = 0 := by
      rw [← Nf_phi, hz, Nf_zmul, Nf_phi, Nf_phi, hxQ, zero_mul]
    have hxz : IsHPair x (zvec x w) := by
      refine isHPair_iff.2 ⟨hxQ, hzQ, ?_⟩
      rw [hz, zmul_alt_left, zmul_phi_self, hxQ]
      simp [zmul_smul_left, zmul_zero_left]
    have hzw : IsHPair (zvec x w) w := by
      refine isHPair_iff.2 ⟨hzQ, hwQ, ?_⟩
      rw [hz, zmul_alt_right, zmul_phi_self, hwQ]
      simp [zmul_smul_right, zmul_zero_right]
    refine ⟨sptOf (zvec x w) hz0 hzQ, ?_, ?_⟩
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair_even hx hxz
      exact ⟨M, h1, sptOf_mem.2 h2⟩
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair_even hz0 hzw
      exact ⟨M, sptOf_mem.2 h1, h2⟩

/-- Every point is joined to every line by a walk of length at most `5`. -/
theorem exists_walk_even [Fintype F] (p : SPt F) (W : HLine F) :
    ∃ w : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Walk (Sum.inl p) (Sum.inr W), w.length ≤ 5 := by
  obtain ⟨w, hwW, hw0, hB⟩ := exists_orth_even p.1.rep W
  have hwQ : Qf w = 0 := Qf_eq_zero_of_mem_hline W hwW
  obtain ⟨m, ⟨M1, h1x, h1m⟩, ⟨M2, h2m, h2w⟩⟩ :=
    exists_mid_even p.1.rep_nonzero p.2 hw0 hwQ hB
  let w' : SPt F := sptOf w hw0 hwQ
  have hw' : w'.1.rep ∈ W.1 := sptOf_mem.2 hwW
  have hw'2 : w'.1.rep ∈ M2.1 := sptOf_mem.2 h2w
  have a1 : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj (Sum.inl p) (Sum.inr M1) :=
    (show hexInc p M1 from h1x)
  have a2 : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj (Sum.inr M1) (Sum.inl m) :=
    (show hexInc m M1 from h1m)
  have a3 : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj (Sum.inl m) (Sum.inr M2) :=
    (show hexInc m M2 from h2m)
  have a4 : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj (Sum.inr M2) (Sum.inl w') :=
    (show hexInc w' M2 from hw'2)
  have a5 : (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj (Sum.inl w') (Sum.inr W) :=
    (show hexInc w' W from hw')
  exact ⟨.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))), by simp⟩

/-- **The split Cayley hexagon `H(q)` for every finite field `F`** (`q = |F|`, any characteristic): the
incidence graph of its points and lines is the incidence graph of a generalized hexagon. -/
theorem genPolygonGraph_hexagon_even [Fintype F] :
    BipartiteDD.Doubling.GenPolygonGraph (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) 6 := by
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline_even (F := F); Fintype.ofFinite _
  exact genPolygonGraph_six hexInc (Fintype.card F) Fintype.card_pos card_lines_through_even
    card_points_hline card_spt_eq exists_walk_even

end BipartiteDD.HexagonEven
