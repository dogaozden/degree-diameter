import BipartiteDD.HexagonEven.Identity
import BipartiteDD.HexagonEven.Pi

/-! Theorem D (even `q`), the hyperplanes `Π_z` (mirror of `HexagonD/PiZ.lean`): for `z = (α, β)`,
`Π_z : x₀ + x₃ + d x₄ + α x₂ + β x₅ = 0` (`InPiZE`), and the plane `π_y ∩ Π_z` of a nonzero singular `y ∈ Π_z`.

`plane_not_piZE`: `π_y` is not contained in `Π_z`. The proof is the one of `plane_not_piE` (`Pi.lean`): the functional
`λ` with `L_z(zvec y w) = λ B(y, w)` would force `(λ² + λ + d)³ y = 0`; the integer determinant of the 7 × 7 system
is `(λ²+λ+d)³` mod 2 (independent of `α, β`); the certificate was computed with sympy. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- `L_z(zvec y w)` as a polynomial (linear in `w`). -/
theorem LzvecZ (d α β : F) (y w : V7 F) :
    (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 + α * (zvec y w) 2 + β * (zvec y w) 5 =
      α*w 2*y 3 - α*w 3*y 2 - α*w 4*y 5 + α*w 5*y 4 + β*w 0*y 2 - β*w 2*y 0 + β*w 3*y 5 - β*w 5*y 3 - d*w 1*y 2 + d*w 2*y 1 + d*w 3*y 4 - d*w 4*y 3 + w 0*y 3 - w 3*y 0 + w 3*y 3 - w 4*y 0 - w 5*y 1 - w 5*y 6 - w 6*y 2 + w 6*y 5 := by
  simp [zvec, zmul, phi]
  ring

/-- The functional `x ↦ x₀ + x₃ + d x₄ + α x₂ + β x₅` (`Π_z`). -/
def LfunZ (d α β : F) : V7 F →ₗ[F] F :=
  (LinearMap.proj 0 : V7 F →ₗ[F] F) + (LinearMap.proj 3 : V7 F →ₗ[F] F) + d • (LinearMap.proj 4 : V7 F →ₗ[F] F) +
    α • (LinearMap.proj 2 : V7 F →ₗ[F] F) + β • (LinearMap.proj 5 : V7 F →ₗ[F] F)

theorem LfunZ_apply (d α β : F) (x : V7 F) : LfunZ d α β x = x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 := by
  simp [LfunZ]

theorem zvec_mem_plane'' {y w : V7 F} (hyQ : Qf y = 0) (hB : Bf y w = 0) : zvec y w ∈ plane y := by
  rw [mem_plane, phi_zvec hB, zmul_alt_left, zmul_phi_self, hyQ]
  simp [zmul_zero_left]

theorem plane_not_piZE {d α β : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) : ∃ z ∈ plane y, z 0 + z 3 + d * z 4 + α * z 2 + β * z 5 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hall' : ∀ w, Bf y w = 0 → (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 + α * (zvec y w) 2 +
      β * (zvec y w) 5 = 0 := fun w hB => hall _ (zvec_mem_plane'' hyQ hB)
  obtain ⟨w0, hw0⟩ : ∃ w0, Bf y w0 ≠ 0 := by
    by_contra h
    push Not at h
    apply hy0
    have a0 := h (Pi.single 4 1)
    have a1 := h (Pi.single 5 1)
    have a2 := h (Pi.single 6 1)
    have a4 := h (Pi.single 0 1)
    have a5 := h (Pi.single 1 1)
    have a6 := h (Pi.single 2 1)
    simp [Bf, Pi.single_apply] at a0 a1 a2 a4 a5 a6
    simp [Qf, a0, a1, a2, a4, a5, a6] at hyQ
    have h3 : y 3 = 0 := by simpa using hyQ
    ext i
    fin_cases i <;> simp [*]
  obtain ⟨lam, key⟩ : ∃ lam : F, ∀ w : V7 F,
      (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 + α * (zvec y w) 2 + β * (zvec y w) 5 =
        lam * Bf y w := by
    refine ⟨((zvec y w0) 0 + (zvec y w0) 3 + d * (zvec y w0) 4 + α * (zvec y w0) 2 + β * (zvec y w0) 5) /
      Bf y w0, fun w => ?_⟩
    set t := Bf y w / Bf y w0 with ht
    have hB' : Bf y (w - t • w0) = 0 := by
      have := (BfForm F y).map_sub w (t • w0)
      rw [(BfForm F y).map_smul] at this
      simp only [BfForm_apply, smul_eq_mul] at this
      rw [this, ht]
      field_simp
      ring
    have h1 := hall' _ hB'
    rw [LzvecZ] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    have e0 := LzvecZ d α β y w0
    have e1 := LzvecZ d α β y w
    have h2' : (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 + α * (zvec y w) 2 + β * (zvec y w) 5 =
        t * ((zvec y w0) 0 + (zvec y w0) 3 + d * (zvec y w0) 4 + α * (zvec y w0) 2 + β * (zvec y w0) 5) := by
      linear_combination e1 - t * e0 + h1
    rw [h2', ht]
    field_simp
  have e0 := key (Pi.single 0 1)
  have e1 := key (Pi.single 1 1)
  have e2 := key (Pi.single 2 1)
  have e3 := key (Pi.single 3 1)
  have e4 := key (Pi.single 4 1)
  have e5 := key (Pi.single 5 1)
  have e6 := key (Pi.single 6 1)
  rw [LzvecZ] at e0 e1 e2 e3 e4 e5 e6
  simp only [Bf, Pi.single_apply] at e0 e1 e2 e3 e4 e5 e6
  norm_num at e0 e1 e2 e3 e4 e5 e6
  have hT : (d + lam ^ 2 + lam) ≠ 0 := fun h => hd lam (by linear_combination h)
  have hT3 : (d + lam ^ 2 + lam) ^ 3 ≠ 0 := pow_ne_zero _ hT
  apply hy0

  have hk0 : (d + lam ^ 2 + lam) ^ 3 * y 0 = 0 := by
    linear_combination (d^4 + 2*d^3*lam^2 + 2*d^3*lam + d^2*lam^4 + 2*d^2*lam^3 + d^2*lam^2) * e0 + (-2*α*d^2*lam - α*d^2 - 4*α*d*lam^3 - 6*α*d*lam^2 - 2*α*d*lam - 2*α*lam^5 - 5*α*lam^4 - 4*α*lam^3 - α*lam^2 + β*d^3 + 2*β*d^2*lam^2 + 2*β*d^2*lam + β*d*lam^4 + 2*β*d*lam^3 + β*d*lam^2) * e1 + (d^3*lam + 2*d^2*lam^3 + 2*d^2*lam^2 + d*lam^5 + 2*d*lam^4 + d*lam^3) * e3 + (d^3 + 4*d^2*lam^2 + 3*d^2*lam + 5*d*lam^4 + 8*d*lam^3 + 3*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e4 + (α*d^3 + 2*α*d^2*lam^2 + 2*α*d^2*lam + α*d*lam^4 + 2*α*d*lam^3 + α*d*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 0 * h2
  have hk1 : (d + lam ^ 2 + lam) ^ 3 * y 1 = 0 := by
    linear_combination (2*α*d^2*lam + α*d^2 + 4*α*d*lam^3 + 6*α*d*lam^2 + 2*α*d*lam + 2*α*lam^5 + 5*α*lam^4 + 4*α*lam^3 + α*lam^2 + β*d^3 + 2*β*d^2*lam^2 + 2*β*d^2*lam + β*d*lam^4 + 2*β*d*lam^3 + β*d*lam^2) * e0 + (β^2*d^2 + 2*β^2*d*lam^2 + 2*β^2*d*lam + β^2*lam^4 + 2*β^2*lam^3 + β^2*lam^2) * e1 + (-2*d^2*lam - d^2 - 4*d*lam^3 - 6*d*lam^2 - 2*d*lam - 2*lam^5 - 5*lam^4 - 4*lam^3 - lam^2) * e2 + (β*d^2*lam + 2*β*d*lam^3 + 2*β*d*lam^2 + β*lam^5 + 2*β*lam^4 + β*lam^3) * e3 + (β*d^2 + 2*β*d*lam^2 + 2*β*d*lam + β*lam^4 + 2*β*lam^3 + β*lam^2) * e4 + (2*d^2*lam^2 + d^2*lam + 4*d*lam^4 + 6*d*lam^3 + 2*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e5 + (α*β*d^2 + 2*α*β*d*lam^2 + 2*α*β*d*lam + α*β*lam^4 + 2*α*β*lam^3 + α*β*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 1 * h2
  have hk2 : (d + lam ^ 2 + lam) ^ 3 * y 2 = 0 := by
    linear_combination (2*d^2*lam + d^2 + 4*d*lam^3 + 6*d*lam^2 + 2*d*lam + 2*lam^5 + 5*lam^4 + 4*lam^3 + lam^2) * e1 + (2*d^2*lam^2 + d^2*lam + 4*d*lam^4 + 6*d*lam^3 + 2*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 2 * h2
  have hk3 : (d + lam ^ 2 + lam) ^ 3 * y 3 = 0 := by
    linear_combination (-d^3*lam - d^3 - 2*d^2*lam^3 - 4*d^2*lam^2 - 2*d^2*lam - d*lam^5 - 3*d*lam^4 - 3*d*lam^3 - d*lam^2) * e0 + (-β*d^2*lam - β*d^2 - 2*β*d*lam^3 - 4*β*d*lam^2 - 2*β*d*lam - β*lam^5 - 3*β*lam^4 - 3*β*lam^3 - β*lam^2) * e1 + (-d^2*lam^2 - d^2*lam - 2*d*lam^4 - 4*d*lam^3 - 2*d*lam^2 - lam^6 - 3*lam^5 - 3*lam^4 - lam^3) * e3 + (d^2*lam + 2*d*lam^3 + 2*d*lam^2 + lam^5 + 2*lam^4 + lam^3) * e4 + (α*d^2*lam + 2*α*d*lam^3 + 2*α*d*lam^2 + α*lam^5 + 2*α*lam^4 + α*lam^3) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 3 * h2
  have hk4 : (d + lam ^ 2 + lam) ^ 3 * y 4 = 0 := by
    linear_combination (d^3 + 4*d^2*lam^2 + 5*d^2*lam + d^2 + 5*d*lam^4 + 12*d*lam^3 + 9*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e0 + (β*d^2 + 2*β*d*lam^2 + 2*β*d*lam + β*lam^4 + 2*β*lam^3 + β*lam^2) * e1 + (-d^2*lam - d^2 - 2*d*lam^3 - 4*d*lam^2 - 2*d*lam - lam^5 - 3*lam^4 - 3*lam^3 - lam^2) * e3 + (d^2 + 2*d*lam^2 + 2*d*lam + lam^4 + 2*lam^3 + lam^2) * e4 + (α*d^2 + 2*α*d*lam^2 + 2*α*d*lam + α*lam^4 + 2*α*lam^3 + α*lam^2 + 2*β*d^2*lam + β*d^2 + 4*β*d*lam^3 + 6*β*d*lam^2 + 2*β*d*lam + 2*β*lam^5 + 5*β*lam^4 + 4*β*lam^3 + β*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 4 * h2
  have hk5 : (d + lam ^ 2 + lam) ^ 3 * y 5 = 0 := by
    linear_combination (2*d^2*lam^2 + 3*d^2*lam + d^2 + 4*d*lam^4 + 10*d*lam^3 + 8*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e1 + (-2*d^3*lam - d^3 - 4*d^2*lam^3 - 6*d^2*lam^2 - 2*d^2*lam - 2*d*lam^5 - 5*d*lam^4 - 4*d*lam^3 - d*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 5 * h2
  have hk6 : (d + lam ^ 2 + lam) ^ 3 * y 6 = 0 := by
    linear_combination (α*d^3 + 2*α*d^2*lam^2 + 2*α*d^2*lam + α*d*lam^4 + 2*α*d*lam^3 + α*d*lam^2) * e0 + (α*β*d^2 + 2*α*β*d*lam^2 + 2*α*β*d*lam + α*β*lam^4 + 2*α*β*lam^3 + α*β*lam^2) * e1 + (2*d^2*lam^2 + 3*d^2*lam + d^2 + 4*d*lam^4 + 10*d*lam^3 + 8*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e2 + (-α*d^2*lam - α*d^2 - 2*α*d*lam^3 - 4*α*d*lam^2 - 2*α*d*lam - α*lam^5 - 3*α*lam^4 - 3*α*lam^3 - α*lam^2) * e3 + (α*d^2 + 2*α*d*lam^2 + 2*α*d*lam + α*lam^4 + 2*α*lam^3 + α*lam^2 - 2*β*d^2*lam - β*d^2 - 4*β*d*lam^3 - 6*β*d*lam^2 - 2*β*d*lam - 2*β*lam^5 - 5*β*lam^4 - 4*β*lam^3 - β*lam^2) * e4 + (2*d^3*lam + d^3 + 4*d^2*lam^3 + 6*d^2*lam^2 + 2*d^2*lam + 2*d*lam^5 + 5*d*lam^4 + 4*d*lam^3 + d*lam^2) * e5 + (α^2*d^2 + 2*α^2*d*lam^2 + 2*α^2*d*lam + α^2*lam^4 + 2*α^2*lam^3 + α^2*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 6 * h2

  have z0 := (mul_eq_zero.1 hk0).resolve_left hT3
  have z1 := (mul_eq_zero.1 hk1).resolve_left hT3
  have z2 := (mul_eq_zero.1 hk2).resolve_left hT3
  have z3 := (mul_eq_zero.1 hk3).resolve_left hT3
  have z4 := (mul_eq_zero.1 hk4).resolve_left hT3
  have z5 := (mul_eq_zero.1 hk5).resolve_left hT3
  have z6 := (mul_eq_zero.1 hk6).resolve_left hT3
  ext i
  fin_cases i <;> simp [*]

/-- The subspace `π_y ∩ Π_z`. -/
def planePiZE (d α β : F) (y : V7 F) : Submodule F (V7 F) := plane y ⊓ LinearMap.ker (LfunZ d α β)

theorem mem_planePiZE {d α β : F} {y z : V7 F} :
    z ∈ planePiZE d α β y ↔ z ∈ plane y ∧ z 0 + z 3 + d * z 4 + α * z 2 + β * z 5 = 0 := by
  simp [planePiZE, LfunZ_apply]

/-- `π_y ∩ Π_z` has dimension exactly `2` (for a nonzero singular `y ∈ Π_z`). -/
theorem finrank_planePiZE {d α β : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 + α * y 2 + β * y 5 = 0) :
    finrank F (planePiZE d α β y) = 2 := by
  let f : plane y →ₗ[F] F := (LfunZ d α β).comp (plane y).subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rwa [finrank_plane_all hy0 hyQ] at this
  have h2' : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 1 ≤ finrank F (LinearMap.range f) := by
    obtain ⟨z, hz, hz'⟩ := plane_not_piZE hd h2 hy0 hyQ (α := α) (β := β)
    have : LinearMap.range f ≠ ⊥ := by
      intro h
      have : f ⟨z, hz⟩ ∈ LinearMap.range f := ⟨⟨z, hz⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hz' (by simpa [f, LfunZ_apply] using this)
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => this (Submodule.finrank_eq_zero.1 h0))
  have h4 : finrank F (LinearMap.ker f) = 2 := by omega
  have e : planePiZE d α β y = (LinearMap.ker f).map (plane y).subtype := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzp, hzL⟩ := mem_planePiZE.1 hz
      exact ⟨⟨z, hzp⟩, by simpa [f, LinearMap.mem_ker, LfunZ_apply] using hzL, rfl⟩
    · rintro ⟨⟨z', hz'⟩, hz'k, rfl⟩
      exact mem_planePiZE.2 ⟨hz', by simpa [f, LinearMap.mem_ker, LfunZ_apply] using hz'k⟩
  rw [e, Submodule.finrank_map_subtype_eq, h4]

/-- A line of `H(q)` in `Π_z` lies in `π_y ∩ Π_z` for each of its nonzero points `y`. -/
theorem InPiZE.le_planePiZE {d α β : F} {W : HLine F} (hW : ∀ x ∈ W.1, x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0)
    {y : V7 F} (hy0 : y ≠ 0) (hyW : y ∈ W.1) : W.1 ≤ planePiZE d α β y := fun z hz =>
  mem_planePiZE.2 ⟨hline_le_plane W hy0 hyW hz, hW z hz⟩

/-- **Uniqueness of the `S_z`-line through a nonzero singular point of `Π_z`.** -/
theorem slineZE_unique {d α β : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 + α * y 2 + β * y 5 = 0) {W W' : HLine F}
    (hW : ∀ x ∈ W.1, x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0)
    (hW' : ∀ x ∈ W'.1, x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0)
    (hyW : y ∈ W.1) (hyW' : y ∈ W'.1) : W = W' := by
  have h2' := finrank_planePiZE hd h2 hy0 hyQ hyL
  have e : ∀ t : HLine F, (∀ x ∈ t.1, x 0 + x 3 + d * x 4 + α * x 2 + β * x 5 = 0) → y ∈ t.1 →
      t.1 = planePiZE d α β y := fun t ht hyt =>
    Submodule.eq_of_le_of_finrank_eq (InPiZE.le_planePiZE ht hy0 hyt) (by rw [h2', t.2.1])
  exact Subtype.ext ((e W hW hyW).trans (e W' hW' hyW').symm)

end BipartiteDD.HexagonEven
