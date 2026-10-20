import BipartiteDD.Hexagon.Zorn

/-! Split Cayley hexagon `H(q)`, part 3: the plane `π_x` of lines through a singular point.

For a nonzero singular `x ∈ F^7` put `π_x = {y | φ x · φ y = 0}` (the kernel of the linear map `y ↦ φ x · φ y`).
Over a field of characteristic `≠ 2`:
* `φ x · φ y = 0` is the same as `IsHPair x y` (`isHPair_iff`): Tits' equations are the vector part of the
  octonion product, and the scalar part is forced to vanish by `x (x y) = x² y = 0`;
* `π_x` is totally singular (`(x y) ȳ = N(y) x`), hence `dim π_x ≤ 3` because `Q(6, q)` has Witt index `3`;
* the image of `y ↦ φ x · φ y` is totally singular in `C8` (composition `N(xy) = N(x) N(y)`), hence has
  dimension `≤ 4`, so `dim π_x ≥ 3` by rank-nullity.
So `dim π_x = 3` (`finrank_plane`). -/

namespace BipartiteDD.Hexagon

open Module

variable {F : Type*} [Field F]

section generic

/-- A totally isotropic subspace of a nondegenerate bilinear space has at most half the dimension. -/
theorem two_mul_finrank_le {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    (B : LinearMap.BilinForm F M) (hB : B.Nondegenerate) (S : Submodule F M)
    (hS : ∀ x ∈ S, ∀ y ∈ S, B x y = 0) : 2 * finrank F S ≤ finrank F M := by
  have hle : S ≤ B.orthogonal S := fun x hx => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact hS n hn x hx
  have h1 := Submodule.finrank_mono hle
  have h2 := LinearMap.BilinForm.finrank_orthogonal hB S
  have h3 : finrank F S ≤ finrank F M := Submodule.finrank_le S
  omega

end generic

/-- `Bf` as a bilinear form on `F^7`. -/
def BfForm (F : Type*) [Field F] : LinearMap.BilinForm F (V7 F) :=
  LinearMap.mk₂ F Bf
    (fun x y z => by simp only [Bf, Pi.add_apply]; ring)
    (fun c x y => by simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y z => by simp only [Bf, Pi.add_apply]; ring)
    (fun c x y => by simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring)

/-- `Bn` as a bilinear form on `C8`. -/
def BnForm (F : Type*) [Field F] : LinearMap.BilinForm F (C8 F) :=
  LinearMap.mk₂ F Bn
    (fun x y z => by simp only [Bn, Pi.add_apply]; ring)
    (fun c x y => by simp only [Bn, Pi.smul_apply, smul_eq_mul]; ring)
    (fun x y z => by simp only [Bn, Pi.add_apply]; ring)
    (fun c x y => by simp only [Bn, Pi.smul_apply, smul_eq_mul]; ring)

@[simp] theorem BfForm_apply (x y : V7 F) : BfForm F x y = Bf x y := rfl
@[simp] theorem BnForm_apply (x y : C8 F) : BnForm F x y = Bn x y := rfl

theorem Bn_comm (x y : C8 F) : Bn x y = Bn y x := by simp only [Bn]; ring

theorem BfForm_nondegenerate [NeZero (2 : F)] : (BfForm F).Nondegenerate := by
  have h : ∀ x : V7 F, (∀ y, Bf x y = 0) → x = 0 := by
    intro x hx
    have h0 := hx (Pi.single 0 1)
    have h1 := hx (Pi.single 1 1)
    have h2 := hx (Pi.single 2 1)
    have h3 := hx (Pi.single 3 1)
    have h4 := hx (Pi.single 4 1)
    have h5 := hx (Pi.single 5 1)
    have h6 := hx (Pi.single 6 1)
    simp [Bf] at h0 h1 h2 h3 h4 h5 h6
    have h3' : x 3 = 0 := h3.resolve_left two_ne_zero
    ext i
    fin_cases i <;> simp [*]
  refine ⟨fun x hx => h x (fun y => by simpa using hx y), fun y hy => h y (fun x => ?_)⟩
  rw [Bf_comm]; simpa using hy x

theorem BnForm_nondegenerate : (BnForm F).Nondegenerate := by
  have h : ∀ x : C8 F, (∀ y, Bn x y = 0) → x = 0 := by
    intro x hx
    have h0 := hx (Pi.single 0 1)
    have h1 := hx (Pi.single 1 1)
    have h2 := hx (Pi.single 2 1)
    have h3 := hx (Pi.single 3 1)
    have h4 := hx (Pi.single 4 1)
    have h5 := hx (Pi.single 5 1)
    have h6 := hx (Pi.single 6 1)
    have h7 := hx (Pi.single 7 1)
    simp [Bn] at h0 h1 h2 h3 h4 h5 h6 h7
    ext i
    fin_cases i <;> simp [*]
  refine ⟨fun x hx => h x (fun y => by simpa using hx y), fun y hy => h y (fun x => ?_)⟩
  rw [Bn_comm]; simpa using hy x

/-- The linear map `y ↦ φ x · φ y`. -/
def Px (x : V7 F) : V7 F →ₗ[F] C8 F where
  toFun y := zmul (phi x) (phi y)
  map_add' y z := by rw [phi_add, zmul_add_right]
  map_smul' c y := by rw [phi_smul, zmul_smul_right]; rfl

theorem Px_apply (x y : V7 F) : Px x y = zmul (phi x) (phi y) := rfl

/-- The plane `π_x`: all `y` with `φ x · φ y = 0`. -/
def plane (x : V7 F) : Submodule F (V7 F) := LinearMap.ker (Px x)

theorem mem_plane {x y : V7 F} : y ∈ plane x ↔ zmul (phi x) (phi y) = 0 := by
  simp [plane, LinearMap.mem_ker, Px_apply]

theorem phi_ne_zero {x : V7 F} (hx : x ≠ 0) : phi x ≠ 0 := by
  intro h
  apply hx
  ext i
  have h0 := congr_fun h 0
  have h1 := congr_fun h 1
  have h2 := congr_fun h 2
  have h3 := congr_fun h 3
  have h4 := congr_fun h 4
  have h5 := congr_fun h 5
  have h6 := congr_fun h 6
  have h7 := congr_fun h 7
  simp [phi] at h0 h1 h2 h3 h4 h5 h6 h7
  fin_cases i <;> simp [*]

theorem zmul_zero_left (y : C8 F) : zmul 0 y = 0 := by
  ext k; fin_cases k <;> simp [zmul]

theorem zmul_zero_right (y : C8 F) : zmul y 0 = 0 := by
  ext k; fin_cases k <;> simp [zmul]

theorem phi_zero : phi (0 : V7 F) = 0 := by
  ext k; fin_cases k <;> simp [phi]

/-- Every point of `π_x` is singular. -/
theorem Qf_eq_zero_of_mem_plane {x y : V7 F} (hx : x ≠ 0) (hy : y ∈ plane x) : Qf y = 0 := by
  rw [mem_plane] at hy
  have h := zmul_zconj_right (phi x) (phi y)
  rw [hy, zmul_zero_left] at h
  have h' : Nf (phi y) • phi x = 0 := h.symm
  rcases smul_eq_zero.1 h' with h0 | h0
  · rwa [Nf_phi] at h0
  · exact absurd h0 (phi_ne_zero hx)

theorem Bf_eq_zero_of_mem_plane {x y z : V7 F} (hx : x ≠ 0) (hy : y ∈ plane x) (hz : z ∈ plane x) :
    Bf y z = 0 := by
  have h := Qf_add y z
  rw [Qf_eq_zero_of_mem_plane hx hy, Qf_eq_zero_of_mem_plane hx hz,
    Qf_eq_zero_of_mem_plane hx ((plane x).add_mem hy hz)] at h
  linear_combination -h

section dim

theorem finrank_V7 : finrank F (V7 F) = 7 := by simp

theorem finrank_C8 : finrank F (C8 F) = 8 := by simp

variable [NeZero (2 : F)]

/-- `dim π_x ≤ 3`. -/
theorem finrank_plane_le {x : V7 F} (hx : x ≠ 0) : finrank F (plane x) ≤ 3 := by
  have h := two_mul_finrank_le (BfForm F) BfForm_nondegenerate (plane x)
    (fun y hy z hz => Bf_eq_zero_of_mem_plane hx hy hz)
  rw [finrank_V7] at h
  omega

/-- `dim π_x ≥ 3` for singular `x`. -/
theorem three_le_finrank_plane {x : V7 F} (hx : Qf x = 0) : 3 ≤ finrank F (plane x) := by
  have hr : ∀ u ∈ LinearMap.range (Px x), Nf u = 0 := by
    rintro _ ⟨y, rfl⟩
    rw [Px_apply, Nf_zmul, Nf_phi, hx, zero_mul]
  have h := two_mul_finrank_le (BnForm F) BnForm_nondegenerate (LinearMap.range (Px x))
    (fun u hu v hv => by
      have h1 := hr _ ((LinearMap.range (Px x)).add_mem hu hv)
      have h2 := Nf_add u v
      rw [hr u hu, hr v hv, h1] at h2
      simpa using h2.symm)
  rw [finrank_C8] at h
  have key : finrank F (LinearMap.range (Px x)) + finrank F (plane x) = 7 := by
    have := LinearMap.finrank_range_add_finrank_ker (Px x)
    rw [finrank_V7] at this
    exact this
  omega

theorem finrank_plane {x : V7 F} (hx : x ≠ 0) (hQ : Qf x = 0) : finrank F (plane x) = 3 :=
  le_antisymm (finrank_plane_le hx) (three_le_finrank_plane hQ)

end dim

end BipartiteDD.Hexagon
