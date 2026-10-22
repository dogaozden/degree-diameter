import BipartiteDD.HexagonEven.Plane
import BipartiteDD.Hexagon.Main

/-! Split Cayley hexagon `H(q)`, even `q`, part 4 (mirror of `HexagonD/Pi.lean`): the hyperplane
`Π_d : x₀ + x₃ + d x₄ = 0` and the Hermitian spread of `Π_d`, in characteristic `2`.

Hypotheses: `h2 : (2 : F) = 0` and `hd : ∀ t, t² + t + d ≠ 0` (the anisotropy of `t² + t + d`, i.e. `Tr d = 1`
over `GF(q)`; this replaces `¬ IsSquare (-c)`).

* `plane_not_piE`: for a nonzero singular `y ∈ Π_d`, the plane `π_y` is not contained in `Π_d`. The proof
  shows that a linear functional `λ` with `L(zvec y w) = λ B(y, w)` would force `(λ² + λ + d)³ · y = 0`
  (the determinant of the 7 × 7 system is `(λ²+λ+d)³` mod 2; the certificate was computed with sympy).
* `finrank_planePiE`: `π_y ∩ Π_d` has dimension exactly `2`;
* `existsUnique_slineE`: every singular point of `Π_d` lies on exactly one line of `H(q)` inside `Π_d`. -/

namespace BipartiteDD.HexagonEven

open BipartiteDD.Hexagon Module Submodule

variable {F : Type*} [Field F]

/-- The linear functional `x ↦ x₀ + x₃ + d x₄` (char `2`: this is `x₀ - x₃ + d x₄`). -/
def LfunE (d : F) : V7 F →ₗ[F] F :=
  (LinearMap.proj 0 : V7 F →ₗ[F] F) + (LinearMap.proj 3 : V7 F →ₗ[F] F) + d • (LinearMap.proj 4 : V7 F →ₗ[F] F)

theorem LfunE_apply (d : F) (x : V7 F) : LfunE d x = x 0 + x 3 + d * x 4 := by
  simp [LfunE]

/-- A line of `H(q)` lying in `Π_d`. -/
def InPiE (d : F) (W : HLine F) : Prop := ∀ x ∈ W.1, x 0 + x 3 + d * x 4 = 0

/-- The lines of `H(q)` in `Π_d`: the Hermitian spread `S_d`. -/
abbrev SLineE (d : F) : Type _ := {W : HLine F // InPiE d W}

/-- `Lzvec`: the functional `L(zvec y w)` is linear in `w`. -/
theorem LzvecE (d : F) (y w : V7 F) :
    (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 =
      -d * w 1 * y 2 + d * w 2 * y 1 + d * w 3 * y 4 - d * w 4 * y 3 + w 0 * y 3 - w 3 * y 0 +
        w 3 * y 3 - w 4 * y 0 - w 5 * y 1 - w 5 * y 6 - w 6 * y 2 + w 6 * y 5 := by
  simp [zvec, zmul, phi]
  ring

theorem zvec_mem_plane' {y w : V7 F} (hyQ : Qf y = 0) (hB : Bf y w = 0) : zvec y w ∈ plane y := by
  rw [mem_plane, phi_zvec hB, zmul_alt_left, zmul_phi_self, hyQ]
  simp [zmul_zero_left]

/-- **Key lemma (even).** For `d` with `t² + t + d ≠ 0` for all `t`, and `char F = 2`, the plane `π_y` of a
nonzero singular `y ∈ Π_d` is not contained in `Π_d`. -/
theorem plane_not_piE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) : ∃ z ∈ plane y, z 0 + z 3 + d * z 4 ≠ 0 := by
  by_contra hall
  push Not at hall
  have hall' : ∀ w, Bf y w = 0 → (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 = 0 := fun w hB =>
    hall _ (zvec_mem_plane' hyQ hB)
  -- some `w₀` with `B(y, w₀) ≠ 0` (otherwise `y` is in the radical of `B`, so `y = c e₃`, `Q y = -c² = 0`)
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
  -- the functional `L ∘ zvec y` is a multiple of `B(y, ·)`
  obtain ⟨lam, key⟩ : ∃ lam : F, ∀ w : V7 F,
      (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 = lam * Bf y w := by
    refine ⟨((zvec y w0) 0 + (zvec y w0) 3 + d * (zvec y w0) 4) / Bf y w0, fun w => ?_⟩
    set t := Bf y w / Bf y w0 with ht
    have hB' : Bf y (w - t • w0) = 0 := by
      have := (BfForm F y).map_sub w (t • w0)
      rw [(BfForm F y).map_smul] at this
      simp only [BfForm_apply, smul_eq_mul] at this
      rw [this, ht]
      field_simp
      ring
    have h1 := hall' _ hB'
    rw [LzvecE] at h1
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1
    have e0 := LzvecE d y w0
    have e1 := LzvecE d y w
    have h2' : (zvec y w) 0 + (zvec y w) 3 + d * (zvec y w) 4 =
        t * ((zvec y w0) 0 + (zvec y w0) 3 + d * (zvec y w0) 4) := by
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
  rw [LzvecE] at e0 e1 e2 e3 e4 e5 e6
  simp only [Bf, Pi.single_apply] at e0 e1 e2 e3 e4 e5 e6
  norm_num at e0 e1 e2 e3 e4 e5 e6
  have hT : (d + lam ^ 2 + lam) ≠ 0 := fun h => hd lam (by linear_combination h)
  have hT3 : (d + lam ^ 2 + lam) ^ 3 ≠ 0 := pow_ne_zero _ hT
  apply hy0

  have hk0 : (d + lam ^ 2 + lam) ^ 3 * y 0 = 0 := by
    linear_combination (d^4 + 2*d^3*lam^2 + 2*d^3*lam + d^2*lam^4 + 2*d^2*lam^3 + d^2*lam^2) * e0 + (d^3*lam + 2*d^2*lam^3 + 2*d^2*lam^2 + d*lam^5 + 2*d*lam^4 + d*lam^3) * e3 + (d^3 + 4*d^2*lam^2 + 3*d^2*lam + 5*d*lam^4 + 8*d*lam^3 + 3*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e4 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 0 * h2
  have hk1 : (d + lam ^ 2 + lam) ^ 3 * y 1 = 0 := by
    linear_combination (-2*d^2*lam - d^2 - 4*d*lam^3 - 6*d*lam^2 - 2*d*lam - 2*lam^5 - 5*lam^4 - 4*lam^3 - lam^2) * e2 + (2*d^2*lam^2 + d^2*lam + 4*d*lam^4 + 6*d*lam^3 + 2*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e5 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 1 * h2
  have hk2 : (d + lam ^ 2 + lam) ^ 3 * y 2 = 0 := by
    linear_combination (2*d^2*lam + d^2 + 4*d*lam^3 + 6*d*lam^2 + 2*d*lam + 2*lam^5 + 5*lam^4 + 4*lam^3 + lam^2) * e1 + (2*d^2*lam^2 + d^2*lam + 4*d*lam^4 + 6*d*lam^3 + 2*d*lam^2 + 2*lam^6 + 5*lam^5 + 4*lam^4 + lam^3) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 2 * h2
  have hk3 : (d + lam ^ 2 + lam) ^ 3 * y 3 = 0 := by
    linear_combination (-d^3*lam - d^3 - 2*d^2*lam^3 - 4*d^2*lam^2 - 2*d^2*lam - d*lam^5 - 3*d*lam^4 - 3*d*lam^3 - d*lam^2) * e0 + (-d^2*lam^2 - d^2*lam - 2*d*lam^4 - 4*d*lam^3 - 2*d*lam^2 - lam^6 - 3*lam^5 - 3*lam^4 - lam^3) * e3 + (d^2*lam + 2*d*lam^3 + 2*d*lam^2 + lam^5 + 2*lam^4 + lam^3) * e4 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 3 * h2
  have hk4 : (d + lam ^ 2 + lam) ^ 3 * y 4 = 0 := by
    linear_combination (d^3 + 4*d^2*lam^2 + 5*d^2*lam + d^2 + 5*d*lam^4 + 12*d*lam^3 + 9*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e0 + (-d^2*lam - d^2 - 2*d*lam^3 - 4*d*lam^2 - 2*d*lam - lam^5 - 3*lam^4 - 3*lam^3 - lam^2) * e3 + (d^2 + 2*d*lam^2 + 2*d*lam + lam^4 + 2*lam^3 + lam^2) * e4 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 4 * h2
  have hk5 : (d + lam ^ 2 + lam) ^ 3 * y 5 = 0 := by
    linear_combination (2*d^2*lam^2 + 3*d^2*lam + d^2 + 4*d*lam^4 + 10*d*lam^3 + 8*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e1 + (-2*d^3*lam - d^3 - 4*d^2*lam^3 - 6*d^2*lam^2 - 2*d^2*lam - 2*d*lam^5 - 5*d*lam^4 - 4*d*lam^3 - d*lam^2) * e6 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 5 * h2
  have hk6 : (d + lam ^ 2 + lam) ^ 3 * y 6 = 0 := by
    linear_combination (2*d^2*lam^2 + 3*d^2*lam + d^2 + 4*d*lam^4 + 10*d*lam^3 + 8*d*lam^2 + 2*d*lam + 2*lam^6 + 7*lam^5 + 9*lam^4 + 5*lam^3 + lam^2) * e2 + (2*d^3*lam + d^3 + 4*d^2*lam^3 + 6*d^2*lam^2 + 2*d^2*lam + 2*d*lam^5 + 5*d*lam^4 + 4*d*lam^3 + d*lam^2) * e5 + (d^3*lam + d^3 + 3*d^2*lam^3 + 6*d^2*lam^2 + 3*d^2*lam + 3*d*lam^5 + 9*d*lam^4 + 9*d*lam^3 + 3*d*lam^2 + lam^7 + 4*lam^6 + 6*lam^5 + 4*lam^4 + lam^3) * y 6 * h2

  have z0 := (mul_eq_zero.1 hk0).resolve_left hT3
  have z1 := (mul_eq_zero.1 hk1).resolve_left hT3
  have z2 := (mul_eq_zero.1 hk2).resolve_left hT3
  have z3 := (mul_eq_zero.1 hk3).resolve_left hT3
  have z4 := (mul_eq_zero.1 hk4).resolve_left hT3
  have z5 := (mul_eq_zero.1 hk5).resolve_left hT3
  have z6 := (mul_eq_zero.1 hk6).resolve_left hT3
  ext i
  fin_cases i <;> simp [*]

/-- The subspace `π_y ∩ Π_d`. -/
def planePiE (d : F) (y : V7 F) : Submodule F (V7 F) := plane y ⊓ LinearMap.ker (LfunE d)

theorem mem_planePiE {d : F} {y z : V7 F} : z ∈ planePiE d y ↔ z ∈ plane y ∧ z 0 + z 3 + d * z 4 = 0 := by
  simp [planePiE, LfunE_apply]

/-- `π_y ∩ Π_d` has dimension exactly `2`. -/
theorem finrank_planePiE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 = 0) :
    finrank F (planePiE d y) = 2 := by
  let f : plane y →ₗ[F] F := (LfunE d).comp (plane y).subtype
  have h1 : finrank F (LinearMap.range f) + finrank F (LinearMap.ker f) = 3 := by
    have := LinearMap.finrank_range_add_finrank_ker f
    rwa [finrank_plane_all hy0 hyQ] at this
  have h2' : finrank F (LinearMap.range f) ≤ 1 := by
    simpa using Submodule.finrank_le (LinearMap.range f)
  have h3 : 1 ≤ finrank F (LinearMap.range f) := by
    obtain ⟨z, hz, hz'⟩ := plane_not_piE hd h2 hy0 hyQ
    have : LinearMap.range f ≠ ⊥ := by
      intro h
      have : f ⟨z, hz⟩ ∈ LinearMap.range f := ⟨⟨z, hz⟩, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hz' (by simpa [f, LfunE_apply] using this)
    exact Nat.one_le_iff_ne_zero.2 (fun h0 => this (Submodule.finrank_eq_zero.1 h0))
  have h4 : finrank F (LinearMap.ker f) = 2 := by omega
  have e : planePiE d y = (LinearMap.ker f).map (plane y).subtype := by
    ext z
    constructor
    · intro hz
      obtain ⟨hzp, hzL⟩ := mem_planePiE.1 hz
      exact ⟨⟨z, hzp⟩, by simpa [f, LinearMap.mem_ker, LfunE_apply] using hzL, rfl⟩
    · rintro ⟨⟨z', hz'⟩, hz'k, rfl⟩
      exact mem_planePiE.2 ⟨hz', by simpa [f, LinearMap.mem_ker, LfunE_apply] using hz'k⟩
  rw [e, Submodule.finrank_map_subtype_eq, h4]

theorem mem_planePiE_self {d : F} {y : V7 F} (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 = 0) :
    y ∈ planePiE d y :=
  mem_planePiE.2 ⟨mem_plane.2 (by rw [zmul_phi_self, hyQ]; simp), hyL⟩

theorem InPiE.le_planePiE {d : F} {W : HLine F} (hW : InPiE d W) {y : V7 F} (hy0 : y ≠ 0)
    (hyW : y ∈ W.1) : W.1 ≤ planePiE d y := fun z hz =>
  mem_planePiE.2 ⟨hline_le_plane W hy0 hyW hz, hW z hz⟩

/-- Existence of an `S_d`-line through a nonzero singular vector of `Π_d`. -/
theorem exists_slineE {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 = 0) :
    ∃ s : SLineE d, y ∈ s.1.1 := by
  have h2' := finrank_planePiE hd h2 hy0 hyQ hyL
  have hnot : ¬ planePiE d y ≤ span F {y} := by
    intro h
    have := Submodule.finrank_mono h
    rw [h2', finrank_span_singleton hy0] at this
    omega
  obtain ⟨z, hz, hz'⟩ := SetLike.not_le_iff_exists.1 hnot
  obtain ⟨hzp, hzL⟩ := mem_planePiE.1 hz
  refine ⟨⟨hlineOf hy0 ((isHPair_iff_mem_plane hy0 hyQ).2 hzp) hz', ?_⟩, subset_span (by simp)⟩
  intro x hx
  have hx' : x ∈ span F {y, z} := hx
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx'
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * hyL + b * hzL

/-- Uniqueness of the `S_d`-line through a nonzero singular vector of `Π_d`. -/
theorem slineE_unique {d : F} (hd : ∀ t : F, t ^ 2 + t + d ≠ 0) (h2 : (2 : F) = 0) {y : V7 F}
    (hy0 : y ≠ 0) (hyQ : Qf y = 0) (hyL : y 0 + y 3 + d * y 4 = 0) {s s' : SLineE d}
    (hs : y ∈ s.1.1) (hs' : y ∈ s'.1.1) : s = s' := by
  have h2' := finrank_planePiE hd h2 hy0 hyQ hyL
  have e : ∀ t : SLineE d, y ∈ t.1.1 → t.1.1 = planePiE d y := fun t ht =>
    Submodule.eq_of_le_of_finrank_eq (InPiE.le_planePiE t.2 hy0 ht) (by rw [h2', t.1.2.1])
  exact Subtype.ext (Subtype.ext ((e s hs).trans (e s' hs').symm))

end BipartiteDD.HexagonEven
