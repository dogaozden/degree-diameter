import BipartiteDD.HexagonD.Spread

/-! Theorem D, slice 2, part 12 (target 4, step 1): the hyperplanes `Π_z : x₀ + c x₄ + α x₂ + β x₅ = 0`,
`z = (α, β)`. The proofs of `Pi.lean` go through verbatim for every `z`: for a nonzero singular `y ∈ Π_z`
the plane `π_y` is not contained in `Π_z` (`exists_plane_not_piZ`), hence `π_y ∩ Π_z` has dimension `2` and
there is at most one line of `H(q)` through `y` inside `Π_z` (`slineZ_unique`); distinct lines of `S_z` are
opposite (`slineZ_opp`). -/

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The linear functional `x ↦ x₀ + c x₄ + α x₂ + β x₅` defining `Π_z`. -/
def Lz (c α β : F) (x : V7 F) : F := x 0 + c * x 4 + α * x 2 + β * x 5

/-- The linear functional as a linear map. -/
def LfunZ (c α β : F) : V7 F →ₗ[F] F :=
  LinearMap.proj 0 + c • LinearMap.proj 4 + α • LinearMap.proj 2 + β • LinearMap.proj 5

theorem LfunZ_apply (c α β : F) (x : V7 F) : LfunZ c α β x = Lz c α β x := by
  simp [LfunZ, Lz]

/-- A line of `H(q)` in `Π_z`. -/
def InPiZ (c α β : F) (W : HLine F) : Prop := ∀ x ∈ W.1, Lz c α β x = 0

theorem LzZvec (c α β : F) (y w : V7 F) :
    Lz c α β (zvec y w) =
      (β * y 2 + y 3) * w 0 + (-c * y 2) * w 1 + (α * y 3 - β * y 0 + c * y 1) * w 2 +
      (-α * y 2 + β * y 5 + c * y 4 - y 0) * w 3 + (-α * y 5 - c * y 3) * w 4 +
      (α * y 4 - β * y 3 - y 6) * w 5 + y 5 * w 6 := by
  simp [Lz, zvec, zmul, phi]
  ring

/-- **Key lemma for `Π_z`.** -/
theorem exists_plane_not_piZ [NeZero (2 : F)] {c : F} (hc : ¬ IsSquare (-c)) (α β : F) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : Lz c α β y = 0) :
    ∃ z ∈ plane y, Lz c α β z ≠ 0 := by
  by_contra hall
  push Not at hall
  have hall' : ∀ w, Bf y w = 0 → Lz c α β (zvec y w) = 0 := fun w hB =>
    hall _ (zvec_mem_plane hyQ hB)
  obtain ⟨w0, hw0⟩ : ∃ w0, Bf y w0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (BfForm_nondegenerate.1 y (fun w => by simpa using h w))
  obtain ⟨lam, key⟩ : ∃ lam : F, ∀ w : V7 F, Lz c α β (zvec y w) = lam * Bf y w := by
    refine ⟨Lz c α β (zvec y w0) / Bf y w0, fun w => ?_⟩
    set t := Bf y w / Bf y w0 with ht
    have hB' : Bf y (w - t • w0) = 0 := by
      have := (BfForm F y).map_sub w (t • w0)
      rw [(BfForm F y).map_smul] at this
      simp only [BfForm_apply, smul_eq_mul] at this
      rw [this, ht]
      field_simp
      ring
    have h1 := hall' _ hB'
    rw [LzZvec] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    have e0 := LzZvec c α β y w0
    have e1 := LzZvec c α β y w
    have h2 : Lz c α β (zvec y w) = t * Lz c α β (zvec y w0) := by
      linear_combination e1 - t * e0 + h1
    rw [h2, ht]
    field_simp
  have e0 := key (Pi.single 0 1)
  have e1 := key (Pi.single 1 1)
  have e2 := key (Pi.single 2 1)
  have e3 := key (Pi.single 3 1)
  have e4 := key (Pi.single 4 1)
  have e5 := key (Pi.single 5 1)
  have e6 := key (Pi.single 6 1)
  simp only [LzZvec, Bf, Pi.single_apply] at e0 e1 e2 e3 e4 e5 e6
  norm_num at e0 e1 e2 e3 e4 e5 e6
  have hne : c + lam ^ 2 ≠ 0 := by
    intro h
    exact hc ⟨lam, by linear_combination -h⟩
  have y2 : y 2 = 0 := by
    have : (c + lam ^ 2) * y 2 = 0 := by linear_combination -e1 - lam * e6
    exact (mul_eq_zero.1 this).resolve_left hne
  have y5 : y 5 = 0 := by rw [e6, y2]; ring
  simp only [Lz] at hyL
  simp only [y2, y5, mul_zero, add_zero, zero_add, neg_zero, sub_zero, zero_sub] at e0 e2 e3 e4 e5 hyL
  have y4 : y 4 = 0 := by
    have : (c + lam ^ 2) * (2 * y 4) = 0 := by linear_combination e3 + hyL - 2 * lam * e0
    exact (mul_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hne)).resolve_left two_ne_zero
  have y3 : y 3 = 0 := by linear_combination e0 + lam * y4
  have y0 : y 0 = 0 := by linear_combination hyL - c * y4
  simp only [y3, y0, y4, mul_zero, add_zero, zero_add, neg_zero, sub_zero, zero_sub] at e2 e5
  have y1 : y 1 = 0 := by
    have : (c + lam ^ 2) * y 1 = 0 := by linear_combination e2 - lam * e5
    exact (mul_eq_zero.1 this).resolve_left hne
  have y6 : y 6 = 0 := by linear_combination -e5 - lam * y1
  apply hy0
  ext i
  fin_cases i <;> simp [*]

/-- The subspace `π_y ∩ Π_z`. -/
def planePiZ (c α β : F) (y : V7 F) : Submodule F (V7 F) := plane y ⊓ LinearMap.ker (LfunZ c α β)

theorem mem_planePiZ {c α β : F} {y z : V7 F} :
    z ∈ planePiZ c α β y ↔ z ∈ plane y ∧ Lz c α β z = 0 := by
  simp [planePiZ, LfunZ_apply]

theorem finrank_planePiZ [NeZero (2 : F)] {c : F} (hc : ¬ IsSquare (-c)) (α β : F) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : Lz c α β y = 0) : finrank F (planePiZ c α β y) = 2 := by
  let f : plane y →ₗ[F] F := (LfunZ c α β).comp (plane y).subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rwa [finrank_plane hy0 hyQ] at this
  have h2 : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 1 ≤ finrank F (LinearMap.range f) := by
    obtain ⟨z, hz, hz'⟩ := exists_plane_not_piZ hc α β hy0 hyQ hyL
    have : LinearMap.range f ≠ ⊥ := by
      intro h
      have : f ⟨z, hz⟩ ∈ LinearMap.range f := ⟨⟨z, hz⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hz' (by simpa [f, LfunZ_apply] using this)
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => this (Submodule.finrank_eq_zero.1 h0))
  have h4 : finrank F (LinearMap.ker f) = 2 := by omega
  have e : planePiZ c α β y = (LinearMap.ker f).map (plane y).subtype := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzp, hzL⟩ := mem_planePiZ.1 hz
      exact ⟨⟨z, hzp⟩, by simpa [f, LinearMap.mem_ker, LfunZ_apply] using hzL, rfl⟩
    · rintro ⟨⟨z', hz'⟩, hz'k, rfl⟩
      exact mem_planePiZ.2 ⟨hz', by simpa [f, LinearMap.mem_ker, LfunZ_apply] using hz'k⟩
  rw [e, Submodule.finrank_map_subtype_eq, h4]

theorem mem_planePiZ_self {c α β : F} {y : V7 F} (hyQ : Qf y = 0) (hyL : Lz c α β y = 0) :
    y ∈ planePiZ c α β y :=
  mem_planePiZ.2 ⟨mem_plane.2 (by rw [zmul_phi_self, hyQ]; simp), hyL⟩

variable [NeZero (2 : F)]

theorem InPiZ.le_planePiZ {c α β : F} {W : HLine F} (hW : InPiZ c α β W) {y : V7 F} (hy0 : y ≠ 0)
    (hyW : y ∈ W.1) : W.1 ≤ planePiZ c α β y := fun z hz =>
  mem_planePiZ.2 ⟨hline_le_plane W hy0 hyW hz, hW z hz⟩

/-- Uniqueness of the `S_z`-line through a nonzero singular vector of `Π_z`. -/
theorem slineZ_unique {c : F} (hc : ¬ IsSquare (-c)) (α β : F) {y : V7 F} (hy0 : y ≠ 0)
    (hyQ : Qf y = 0) (hyL : Lz c α β y = 0) {s s' : HLine F} (hs : InPiZ c α β s)
    (hs' : InPiZ c α β s') (hys : y ∈ s.1) (hys' : y ∈ s'.1) : s = s' := by
  have h2 := finrank_planePiZ hc α β hy0 hyQ hyL
  have e : ∀ t : HLine F, InPiZ c α β t → y ∈ t.1 → t.1 = planePiZ c α β y := fun t ht hyt =>
    Submodule.eq_of_le_of_finrank_eq (ht.le_planePiZ hy0 hyt) (by rw [h2, t.2.1])
  exact Subtype.ext ((e s hs hys).trans (e s' hs' hys').symm)

/-- Distinct lines of `S_z` are far apart. -/
theorem slineZ_opp {c : F} (hc : ¬ IsSquare (-c)) (α β : F) {s s' : HLine F}
    (hs : InPiZ c α β s) (hs' : InPiZ c α β s') (hne : s ≠ s') [Fintype F] :
    Opp (hexInc (F := F)) s s' := by
  rintro ⟨p, M, p', h1, h2, h3, h4⟩
  have h1' : p.1.rep ∈ s.1 := h1
  have h2' : p.1.rep ∈ M.1 := h2
  have h3' : p'.1.rep ∈ M.1 := h3
  have h4' : p'.1.rep ∈ s'.1 := h4
  have hpL : Lz c α β p.1.rep = 0 := hs _ h1'
  have hp'L : Lz c α β p'.1.rep = 0 := hs' _ h4'
  by_cases hpp : p = p'
  · subst hpp
    exact hne (slineZ_unique hc α β p.1.rep_nonzero p.2 hpL hs hs' h1' h4')
  · have hMspan : M.1 = span F {p.1.rep, p'.1.rep} :=
      hline_eq_span M h2' h3' p.1.rep_nonzero (rep_not_mem_span_of_ne (fun h => hpp (Subtype.ext h)))
    have hM : InPiZ c α β M := by
      intro x hx
      rw [hMspan] at hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      simp only [Lz, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hpL hp'L ⊢
      linear_combination a * hpL + b * hp'L
    have e1 := slineZ_unique hc α β p.1.rep_nonzero p.2 hpL hM hs h2' h1'
    have e2 := slineZ_unique hc α β p'.1.rep_nonzero p'.2 hp'L hM hs' h3' h4'
    exact hne (e1.symm.trans e2)

end BipartiteDD.HexagonD
