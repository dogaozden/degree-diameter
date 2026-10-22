import BipartiteDD.Hexagon.Through
import BipartiteDD.Hexagon.Moore

/-! Split Cayley hexagon `H(q)`, part 7: the incidence graph is a generalized hexagon.

Points are the singular points of `Q(6, q)` (`SPt F`), lines are the `HLine F`, and a point is on a line when
its representative vector lies in the line's subspace. By `genPolygonGraph_six` (a Moore-type counting
theorem) it suffices to know the local counts (`q + 1` lines per point and points per line, `(q⁶-1)/(q-1)`
points) and that every point is joined to every line by a walk of length at most `5`.

That last fact is `exists_walk`: for a point `x` and a line `W` pick `w ∈ W` with `B(x, w) = 0` (a linear form
on the 2-dimensional `W` has a kernel). Then `z = φ⁻¹(φ x · φ w)` is a singular point collinear with both
`x` and `w` (`x (x w) = x² w = 0` and `(x w) w = x w² = 0` in the octonion algebra), so
`x – line – z – line – w – W` is a walk of length `5`. -/

namespace BipartiteDD.Hexagon

open Module Submodule
open scoped Classical

variable {F : Type*} [Field F]

/-- Incidence: the representative of a point lies in the subspace of the line. -/
def hexInc (p : SPt F) (W : HLine F) : Prop := p.1.rep ∈ W.1

/-- The vector with `φ z = φ x · φ w` (when `B(x, w) = 0`). -/
def zvec (x w : V7 F) : V7 F :=
  ![-(zmul (phi x) (phi w) 2), -(zmul (phi x) (phi w) 3), -(zmul (phi x) (phi w) 4),
    zmul (phi x) (phi w) 0, zmul (phi x) (phi w) 5, zmul (phi x) (phi w) 6, zmul (phi x) (phi w) 7]

theorem phi_zvec_aux (P : C8 F) (h : P 0 + P 1 = 0) :
    phi ![-(P 2), -(P 3), -(P 4), P 0, P 5, P 6, P 7] = P := by
  ext k
  fin_cases k <;> simp [phi]
  linear_combination -h

theorem phi_zvec {x w : V7 F} (hB : Bf x w = 0) : phi (zvec x w) = zmul (phi x) (phi w) := by
  have e : zmul (phi x) (phi w) 0 + zmul (phi x) (phi w) 1 = - Bf x w := by
    simp [zmul, phi, Bf]; ring
  exact phi_zvec_aux _ (by rw [e, hB, neg_zero])

/-- The singular point spanned by a nonzero singular vector. -/
def sptOf (v : V7 F) (hv : v ≠ 0) (hQ : Qf v = 0) : SPt F :=
  ⟨Projectivization.mk F v hv, (Qf_rep_eq_zero_iff v hv).2 hQ⟩

theorem sptOf_mem {v : V7 F} {hv : v ≠ 0} {hQ : Qf v = 0} {W : Submodule F (V7 F)} :
    (sptOf v hv hQ).1.rep ∈ W ↔ v ∈ W := rep_mem_iff W v hv

section

variable [Fintype F]

theorem exists_hline_through {x : V7 F} (hx : x ≠ 0) (hQ : Qf x = 0) : ∃ M : HLine F, x ∈ M.1 := by
  have hnot : ¬ plane x ≤ span F {x} := by
    intro h
    have := Submodule.finrank_mono h
    rw [finrank_plane hx hQ, finrank_span_singleton hx] at this
    omega
  obtain ⟨y, hy, hy'⟩ := SetLike.not_le_iff_exists.1 hnot
  exact ⟨hlineOf hx ((isHPair_iff_mem_plane hx hQ).2 hy) hy', subset_span (by simp)⟩

theorem exists_hline_of_isHPair {a b : V7 F} (ha : a ≠ 0) (h : IsHPair a b) :
    ∃ M : HLine F, a ∈ M.1 ∧ b ∈ M.1 := by
  by_cases hb : b ∈ span F {a}
  · obtain ⟨M, hM⟩ := exists_hline_through ha h.1
    refine ⟨M, hM, ?_⟩
    have : span F {a} ≤ M.1 := span_le.2 (by simpa using hM)
    exact this hb
  · exact ⟨hlineOf ha h hb, subset_span (by simp), subset_span (by simp)⟩

/-- Every line has a nonzero vector orthogonal to a given vector. -/
theorem exists_orth (x : V7 F) (W : HLine F) : ∃ w ∈ W.1, w ≠ 0 ∧ Bf x w = 0 := by
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

theorem exists_mid {x w : V7 F} (hx : x ≠ 0) (hxQ : Qf x = 0) (hw : w ≠ 0) (hwQ : Qf w = 0)
    (hB : Bf x w = 0) :
    ∃ m : SPt F, (∃ M : HLine F, x ∈ M.1 ∧ m.1.rep ∈ M.1) ∧ (∃ M : HLine F, m.1.rep ∈ M.1 ∧ w ∈ M.1) := by
  have hz := phi_zvec hB
  by_cases hz0 : zvec x w = 0
  · rw [hz0, phi_zero] at hz
    have hxw : IsHPair x w := isHPair_iff.2 ⟨hxQ, hwQ, hz.symm⟩
    refine ⟨sptOf x hx hxQ, ?_, ?_⟩
    · obtain ⟨M, hM⟩ := exists_hline_through hx hxQ
      exact ⟨M, hM, sptOf_mem.2 hM⟩
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair hx hxw
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
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair hx hxz
      exact ⟨M, h1, sptOf_mem.2 h2⟩
    · obtain ⟨M, h1, h2⟩ := exists_hline_of_isHPair hz0 hzw
      exact ⟨M, sptOf_mem.2 h1, h2⟩

/-- Every point is joined to every line by a walk of length at most `5`. -/
theorem exists_walk (p : SPt F) (W : HLine F) :
    ∃ w : (incGraph (hexInc (F := F))).Walk (Sum.inl p) (Sum.inr W), w.length ≤ 5 := by
  obtain ⟨w, hwW, hw0, hB⟩ := exists_orth p.1.rep W
  have hwQ : Qf w = 0 := Qf_eq_zero_of_mem_hline W hwW
  obtain ⟨m, ⟨M1, h1x, h1m⟩, ⟨M2, h2m, h2w⟩⟩ :=
    exists_mid p.1.rep_nonzero p.2 hw0 hwQ hB
  let w' : SPt F := sptOf w hw0 hwQ
  have hw' : w'.1.rep ∈ W.1 := sptOf_mem.2 hwW
  have hw'2 : w'.1.rep ∈ M2.1 := sptOf_mem.2 h2w
  have a1 : (incGraph (hexInc (F := F))).Adj (Sum.inl p) (Sum.inr M1) :=
    incGraph_adj_inl_inr.2 (show hexInc p M1 from h1x)
  have a2 : (incGraph (hexInc (F := F))).Adj (Sum.inr M1) (Sum.inl m) :=
    incGraph_adj_inr_inl.2 (show hexInc m M1 from h1m)
  have a3 : (incGraph (hexInc (F := F))).Adj (Sum.inl m) (Sum.inr M2) :=
    incGraph_adj_inl_inr.2 (show hexInc m M2 from h2m)
  have a4 : (incGraph (hexInc (F := F))).Adj (Sum.inr M2) (Sum.inl w') :=
    incGraph_adj_inr_inl.2 (show hexInc w' M2 from hw'2)
  have a5 : (incGraph (hexInc (F := F))).Adj (Sum.inl w') (Sum.inr W) :=
    incGraph_adj_inl_inr.2 (show hexInc w' W from hw')
  exact ⟨.cons a1 (.cons a2 (.cons a3 (.cons a4 (.cons a5 .nil)))), by simp⟩

theorem finite_spt' : Finite (SPt F) := inferInstance

/-- **The split Cayley hexagon.** For a finite field `F` of odd characteristic, the incidence graph of
the points and lines of `H(q)` (`q = |F|`) is the incidence graph of a generalized hexagon. -/
theorem genPolygonGraph_hexagon :
    BipartiteDD.Doubling.GenPolygonGraph (incGraph (hexInc (F := F))) 6 := by
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline (F := F); Fintype.ofFinite _
  exact genPolygonGraph_six hexInc (Fintype.card F) Fintype.card_pos card_lines_through
    card_points_hline card_spt_eq exists_walk

/-- `H(q)` has as many lines as points: `(q⁶ - 1)/(q - 1)`. -/
theorem card_hline : Nat.card (HLine F) = (Fintype.card F ^ 6 - 1) / (Fintype.card F - 1) := by
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline (F := F); Fintype.ofFinite _
  rw [← card_spt_div]
  exact (card_lines_eq (inc := hexInc (F := F)) (k := Fintype.card F + 1) (by omega)
    card_lines_through card_points_hline).symm ▸ rfl

end

end BipartiteDD.Hexagon
