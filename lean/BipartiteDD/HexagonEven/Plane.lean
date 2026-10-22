import BipartiteDD.Hexagon.Plane

/-! Split Cayley hexagon `H(q)` for every finite field, part 1: the planes `π_x` in characteristic `2`.

`BipartiteDD.Hexagon.finrank_plane` needs `(2 : F) ≠ 0`, because the form `Bf` is nondegenerate only then.
Here `dim π_x = 3` is proved for every field:
* if `(2 : F) ≠ 0`, the old result applies (`NeZero (2 : F)` is supplied by `haveI`);
* if `(2 : F) = 0`, the form `Bf` has radical `⟨e₃⟩`, but `Q(e₃) = -1 ≠ 0`. So the projection
  `y ↦ (y₀, y₁, y₂, y₄, y₅, y₆)` is injective on the totally singular `π_x` (`Qf y = 0` and the projection
  zero force `y₃² = 0`). Its image is totally isotropic for the nondegenerate symplectic form `B6` on `F⁶`
  (in characteristic `2`, `B6 (proj y) (proj z) = Bf y z`), so it has dimension `≤ 3`.
The lower bound `dim π_x ≥ 3` never used a characteristic hypothesis. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module

variable {F : Type*} [Field F]

/-- Forget the coordinate `y₃`. -/
def proj6 (y : V7 F) : Fin 6 → F := ![y 0, y 1, y 2, y 4, y 5, y 6]

/-- The projection `F⁷ → F⁶`, as a linear map. -/
def proj6L : V7 F →ₗ[F] (Fin 6 → F) where
  toFun := proj6
  map_add' a b := by ext i; fin_cases i <;> simp [proj6]
  map_smul' c a := by ext i; fin_cases i <;> simp [proj6]

/-- The symplectic form `u₀v₃ + u₃v₀ + u₁v₄ + u₄v₁ + u₂v₅ + u₅v₂` on `F⁶`. -/
def B6 (u v : Fin 6 → F) : F :=
  u 0 * v 3 + u 3 * v 0 + u 1 * v 4 + u 4 * v 1 + u 2 * v 5 + u 5 * v 2

theorem B6_comm (u v : Fin 6 → F) : B6 u v = B6 v u := by
  simp only [B6]; ring

theorem B6_add_right (u v w : Fin 6 → F) : B6 u (v + w) = B6 u v + B6 u w := by
  simp only [B6, Pi.add_apply]; ring

theorem B6_add_left (u v w : Fin 6 → F) : B6 (u + v) w = B6 u w + B6 v w := by
  simp only [B6, Pi.add_apply]; ring

theorem B6_smul_right (c : F) (u v : Fin 6 → F) : B6 u (c • v) = c * B6 u v := by
  simp only [B6, Pi.smul_apply, smul_eq_mul]; ring

theorem B6_smul_left (c : F) (u v : Fin 6 → F) : B6 (c • u) v = c * B6 u v := by
  simp only [B6, Pi.smul_apply, smul_eq_mul]; ring

/-- `B6` as a bilinear form on `F⁶`. -/
def B6Form (F : Type*) [Field F] : LinearMap.BilinForm F (Fin 6 → F) :=
  LinearMap.mk₂ F B6 B6_add_left B6_smul_left B6_add_right B6_smul_right

@[simp] theorem B6Form_apply (u v : Fin 6 → F) : B6Form F u v = B6 u v := rfl

theorem B6Form_nondegenerate : (B6Form F).Nondegenerate := by
  have h : ∀ u : Fin 6 → F, (∀ v, B6 u v = 0) → u = 0 := by
    intro u hu
    have h0 := hu (Pi.single 3 1)
    have h1 := hu (Pi.single 0 1)
    have h2 := hu (Pi.single 4 1)
    have h3 := hu (Pi.single 1 1)
    have h4 := hu (Pi.single 5 1)
    have h5 := hu (Pi.single 2 1)
    simp [B6] at h0 h1 h2 h3 h4 h5
    ext i
    fin_cases i <;> simp [*]
  refine ⟨fun u hu => h u (fun v => by simpa using hu v), fun v hv => h v (fun u => ?_)⟩
  rw [B6_comm]; simpa using hv u

section char2

theorem proj6L_apply (y : V7 F) : proj6L y = proj6 y := rfl

/-- Totally singular planes: the projection to `F⁶` is injective on `π_x` (for `x ≠ 0`). -/
theorem proj_ker_bot {x : V7 F} (hx : x ≠ 0) :
    LinearMap.ker ((proj6L (F := F)).comp (plane x).subtype) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro y hy
  have hy' : proj6 y.1 = 0 := hy
  have hQy : Qf y.1 = 0 := Qf_eq_zero_of_mem_plane hx y.2
  have h0 : y.1 0 = 0 := congr_fun hy' 0
  have h1 : y.1 1 = 0 := congr_fun hy' 1
  have h2 : y.1 2 = 0 := congr_fun hy' 2
  have h4 : y.1 4 = 0 := congr_fun hy' 3
  have h5 : y.1 5 = 0 := congr_fun hy' 4
  have h6 : y.1 6 = 0 := congr_fun hy' 5
  have h3 : y.1 3 ^ 2 = 0 := by
    unfold Qf at hQy
    rw [h0, h1, h2, h4, h5, h6] at hQy
    linear_combination -hQy
  have h3' : y.1 3 = 0 := pow_eq_zero_iff two_ne_zero |>.mp h3
  apply Subtype.ext
  ext i
  fin_cases i <;> simp [h0, h1, h2, h3', h4, h5, h6]

end char2

section dim

/-- A Witt-type bound valid in every characteristic: `dim π_x ≤ 3` when `(2 : F) = 0`. -/
theorem finrank_plane_char2 (h2 : (2 : F) = 0) {x : V7 F} (hx : x ≠ 0) :
    finrank F (plane x) ≤ 3 := by
  set f := (proj6L (F := F)).comp (plane x).subtype with hf
  have hker := proj_ker_bot hx
  have hiso : ∀ u ∈ LinearMap.range f, ∀ v ∈ LinearMap.range f, B6Form F u v = 0 := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have ha : Bf a.1 b.1 = 0 := Bf_eq_zero_of_mem_plane hx a.2 b.2
    have e : B6 (f a) (f b) = Bf a.1 b.1 + 2 * (a.1 3 * b.1 3) := by
      simp only [hf, LinearMap.comp_apply, Submodule.subtype_apply, proj6L_apply]
      simp [B6, proj6, Bf]
    rw [B6Form_apply, e, ha, h2, zero_mul, add_zero]
  have hrk : 2 * finrank F (LinearMap.range f) ≤ finrank F (Fin 6 → F) :=
    two_mul_finrank_le (B6Form F) B6Form_nondegenerate (LinearMap.range f) hiso
  have hfin : finrank F (plane x) = finrank F (LinearMap.range f) := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rw [hker, finrank_bot, add_zero] at this
    exact this.symm
  have h6 : finrank F (Fin 6 → F) = 6 := by simp
  omega

/-- `dim π_x ≥ 3` for singular `x` (no characteristic hypothesis; same proof as the master file). -/
theorem three_le_finrank_plane_all {x : V7 F} (hx : Qf x = 0) : 3 ≤ finrank F (plane x) := by
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

/-- **`dim π_x = 3` in every characteristic.** -/
theorem finrank_plane_all {x : V7 F} (hx : x ≠ 0) (hQ : Qf x = 0) : finrank F (plane x) = 3 := by
  refine le_antisymm ?_ (three_le_finrank_plane_all hQ)
  by_cases h2 : (2 : F) = 0
  · exact finrank_plane_char2 h2 hx
  · haveI : NeZero (2 : F) := ⟨h2⟩
    exact finrank_plane_le hx

end dim

end BipartiteDD.HexagonEven
