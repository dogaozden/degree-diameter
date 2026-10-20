import BipartiteDD.Hexagon.Main

/-! Theorem D, slice 2, part 1: the hyperplane `Π : x₀ + c x₄ = 0` and the Hermitian spread.

Let `F` be a field of characteristic `≠ 2` and `c ∈ F` with `-c` a non-square. The hyperplane
`Π = {x | x₀ + c x₄ = 0}` has pole `c e₀ + e₄` of norm `c`, and `Q|Π` is a hyperbolic 4-space plus the
anisotropic plane `x₃² + c x₄²`.

Main results (`F` finite for the counts, in later files):
* `exists_plane_not_pi`: for a nonzero singular `y ∈ Π` the plane `π_y` is not contained in `Π`
  (the only place where the non-squareness of `-c` is used);
* `finrank_planePi`: hence `π_y ∩ Π` has dimension exactly `2`;
* `existsUnique_sline`: every singular point of `Π` lies on exactly one `H(q)`-line contained in `Π`
  (so the set `S` of these lines is a spread of `Π ∩ Q`). -/

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The linear functional `x ↦ x₀ + c x₄` defining `Π`. -/
def Lfun (c : F) : V7 F →ₗ[F] F := LinearMap.proj 0 + c • LinearMap.proj 4

theorem Lfun_apply (c : F) (x : V7 F) : Lfun c x = x 0 + c * x 4 := by
  simp [Lfun]

/-- A line of `H(q)` lying in the hyperplane `Π`. -/
def InPi (c : F) (W : HLine F) : Prop := ∀ x ∈ W.1, x 0 + c * x 4 = 0

/-- The lines of `H(q)` in `Π`: the Hermitian spread `S`. -/
abbrev SLine (c : F) : Type _ := {W : HLine F // InPi c W}

theorem Lzvec (c : F) (y w : V7 F) :
    (zvec y w) 0 + c * (zvec y w) 4 =
      y 3 * w 0 - c * y 2 * w 1 + c * y 1 * w 2 + (c * y 4 - y 0) * w 3 - c * y 3 * w 4 -
        y 6 * w 5 + y 5 * w 6 := by
  simp [zvec, zmul, phi]
  ring

theorem zvec_mem_plane {y w : V7 F} (hyQ : Qf y = 0) (hB : Bf y w = 0) : zvec y w ∈ plane y := by
  rw [mem_plane, phi_zvec hB, zmul_alt_left, zmul_phi_self, hyQ]
  simp [zmul_zero_left]

/-- **Key lemma.** For `-c` a non-square, the plane `π_y` of a nonzero singular `y ∈ Π` is not
contained in `Π`. -/
theorem exists_plane_not_pi [NeZero (2 : F)] {c : F} (hc : ¬ IsSquare (-c)) {y : V7 F} (hy0 : y ≠ 0)
    (hyQ : Qf y = 0) (hyL : y 0 + c * y 4 = 0) : ∃ z ∈ plane y, z 0 + c * z 4 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hall' : ∀ w, Bf y w = 0 → (zvec y w) 0 + c * (zvec y w) 4 = 0 := fun w hB =>
    hall _ (zvec_mem_plane hyQ hB)
  -- some `w₀` with `B(y, w₀) ≠ 0`
  obtain ⟨w0, hw0⟩ : ∃ w0, Bf y w0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hy0 (BfForm_nondegenerate.1 y (fun w => by simpa using h w))
  -- the functional `f` vanishes on the kernel of `g = B(y, ·)`, so `f = λ g`
  obtain ⟨lam, key⟩ : ∃ lam : F, ∀ w : V7 F, (zvec y w) 0 + c * (zvec y w) 4 = lam * Bf y w := by
    refine ⟨((zvec y w0) 0 + c * (zvec y w0) 4) / Bf y w0, fun w => ?_⟩
    set t := Bf y w / Bf y w0 with ht
    have hB' : Bf y (w - t • w0) = 0 := by
      have := (BfForm F y).map_sub w (t • w0)
      rw [(BfForm F y).map_smul] at this
      simp only [BfForm_apply, smul_eq_mul] at this
      rw [this, ht]
      field_simp
      ring
    have h1 := hall' _ hB'
    rw [Lzvec] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    have e0 := Lzvec c y w0
    have e1 := Lzvec c y w
    have h2 : (zvec y w) 0 + c * (zvec y w) 4 = t * ((zvec y w0) 0 + c * (zvec y w0) 4) := by
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
  simp only [Lzvec, Bf, Pi.single_apply] at e0 e1 e2 e3 e4 e5 e6
  norm_num at e0 e1 e2 e3 e4 e5 e6
  have hne : c + lam ^ 2 ≠ 0 := by
    intro h
    exact hc ⟨lam, by linear_combination -h⟩
  have y4 : y 4 = 0 := by
    have : (c + lam ^ 2) * (2 * y 4) = 0 := by
      linear_combination e3 - 2 * lam * e0 + hyL
    exact (mul_eq_zero.1 this).resolve_left hne |> fun h => (mul_eq_zero.1 h).resolve_left two_ne_zero
  have y3 : y 3 = 0 := by rw [e0, y4]; ring
  have y0 : y 0 = 0 := by linear_combination hyL - c * y4
  have y2 : y 2 = 0 := by
    have : (c + lam ^ 2) * y 2 = 0 := by linear_combination -e1 - lam * e6
    exact (mul_eq_zero.1 this).resolve_left hne
  have y5 : y 5 = 0 := by rw [e6, y2]; ring
  have y1 : y 1 = 0 := by
    have : (c + lam ^ 2) * y 1 = 0 := by linear_combination e2 - lam * e5
    exact (mul_eq_zero.1 this).resolve_left hne
  have y6 : y 6 = 0 := by linear_combination -e5 - lam * y1
  apply hy0
  ext i
  fin_cases i <;> simp [*]

/-- The subspace `π_y ∩ Π`. -/
def planePi (c : F) (y : V7 F) : Submodule F (V7 F) := plane y ⊓ LinearMap.ker (Lfun c)

theorem mem_planePi {c : F} {y z : V7 F} : z ∈ planePi c y ↔ z ∈ plane y ∧ z 0 + c * z 4 = 0 := by
  simp [planePi, Lfun_apply]

/-- `π_y ∩ Π` has dimension exactly `2`. -/
theorem finrank_planePi [NeZero (2 : F)] {c : F} (hc : ¬ IsSquare (-c)) {y : V7 F} (hy0 : y ≠ 0)
    (hyQ : Qf y = 0) (hyL : y 0 + c * y 4 = 0) : finrank F (planePi c y) = 2 := by
  let f : plane y →ₗ[F] F := (Lfun c).comp (plane y).subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rwa [finrank_plane hy0 hyQ] at this
  have h2 : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 1 ≤ finrank F (LinearMap.range f) := by
    obtain ⟨z, hz, hz'⟩ := exists_plane_not_pi hc hy0 hyQ hyL
    have : LinearMap.range f ≠ ⊥ := by
      intro h
      have : f ⟨z, hz⟩ ∈ LinearMap.range f := ⟨⟨z, hz⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hz' (by simpa [f, Lfun_apply] using this)
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => this (Submodule.finrank_eq_zero.1 h0))
  have h4 : finrank F (LinearMap.ker f) = 2 := by omega
  -- identify `planePi` with the image of `ker f`
  have e : planePi c y = (LinearMap.ker f).map (plane y).subtype := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzp, hzL⟩ := mem_planePi.1 hz
      exact ⟨⟨z, hzp⟩, by simpa [f, LinearMap.mem_ker, Lfun_apply] using hzL, rfl⟩
    · rintro ⟨⟨z', hz'⟩, hz'k, rfl⟩
      exact mem_planePi.2 ⟨hz', by simpa [f, LinearMap.mem_ker, Lfun_apply] using hz'k⟩
  rw [e, Submodule.finrank_map_subtype_eq, h4]

theorem mem_planePi_self {c : F} {y : V7 F} (hyQ : Qf y = 0) (hyL : y 0 + c * y 4 = 0) :
    y ∈ planePi c y :=
  mem_planePi.2 ⟨mem_plane.2 (by rw [zmul_phi_self, hyQ]; simp), hyL⟩

variable [NeZero (2 : F)]

omit [NeZero (2 : F)] in
theorem InPi.le_planePi {c : F} {W : HLine F} (hW : InPi c W) {y : V7 F} (hy0 : y ≠ 0)
    (hyW : y ∈ W.1) : W.1 ≤ planePi c y := fun z hz =>
  mem_planePi.2 ⟨hline_le_plane W hy0 hyW hz, hW z hz⟩

/-- Existence of an `S`-line through a nonzero singular vector of `Π`. -/
theorem exists_sline {c : F} (hc : ¬ IsSquare (-c)) {y : V7 F} (hy0 : y ≠ 0) (hyQ : Qf y = 0)
    (hyL : y 0 + c * y 4 = 0) : ∃ s : SLine c, y ∈ s.1.1 := by
  have h2 := finrank_planePi hc hy0 hyQ hyL
  have hnot : ¬ planePi c y ≤ span F {y} := by
    intro h
    have := Submodule.finrank_mono h
    rw [h2, finrank_span_singleton hy0] at this
    omega
  obtain ⟨z, hz, hz'⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨hzp, hzL⟩ := mem_planePi.1 hz
  refine ⟨⟨hlineOf hy0 ((isHPair_iff_mem_plane hy0 hyQ).2 hzp) hz', ?_⟩, subset_span (by simp)⟩
  intro x hx
  have hx' : x ∈ span F {y, z} := hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * hyL + b * hzL

/-- Uniqueness of the `S`-line through a nonzero singular vector of `Π`. -/
theorem sline_unique {c : F} (hc : ¬ IsSquare (-c)) {y : V7 F} (hy0 : y ≠ 0) (hyQ : Qf y = 0)
    (hyL : y 0 + c * y 4 = 0) {s s' : SLine c} (hs : y ∈ s.1.1) (hs' : y ∈ s'.1.1) : s = s' := by
  have h2 := finrank_planePi hc hy0 hyQ hyL
  have e : ∀ t : SLine c, y ∈ t.1.1 → t.1.1 = planePi c y := fun t ht =>
    Submodule.eq_of_le_of_finrank_eq (t.2.le_planePi hy0 ht) (by rw [h2, t.1.2.1])
  exact Subtype.ext (Subtype.ext ((e s hs).trans (e s' hs').symm))

end BipartiteDD.HexagonD
