import BipartiteDD.LeanMaxx.Omega45b.Diag7
import BipartiteDD.LeanMaxx.Omega45b.QuadCount

/-!
# Omega45b.CharSum: `#{Q = 0, b(v, Tv) = 0} ≤ q^5 + (q-1) Σ_c q^{(3+d_c)/2}` for `q = 7`

Setting (research/theorems/OMEGA_REPAIR.md, Lemma 4.4). `T` is a linear isometry of `(F7^7, Qf)`,
`F v = Bf v (T v)`, `R_c = F - c·Qf` and `d_c = dim ker (T + T⁻¹ - c)`.

Route (equivalent to the character-sum argument, but with the exponential sums replaced by exact zero
counts, so everything stays in `ℕ`):
* `sum_card_Rc`: `Σ_c #{R_c = 0} = 7·N + #{Qf ≠ 0}`, since a vector with `Qf v ≠ 0` is a zero of
  exactly one `R_c` (`c = F v / Qf v`), and a vector with `Qf v = 0` is a zero of all `R_c` or of none.
* `RcQ_polar`: the polar form of `R_c` is `(v, u) ↦ Bf v ((T + T⁻¹ - c) u)`, so by nondegeneracy of
  `Bf` its radical is `ker (T + T⁻¹ - c)`, of size `7 ^ d_c`.
* `quad_zeros_good`: any quadratic form on `F7^7` whose polar radical has `7^k` elements has exactly
  `7^6` zeros when `k` is even and at most `7^6 + 6·7^((5+k)/2)` zeros when `k` is odd
  (diagonalise, then `Diag7.wzeros7`). This is the `|Σ_v ψ(b R v)| = q^{7 - r/2}` step.
* Combining: `7 N + 7^7 - 7^6 ≤ 7·7^6 + 6 Σ_c 7^((5+d_c)/2)`.

`sum_dk_le`: `Σ_c d_c ≤ 7` (eigenspaces of `T + T⁻¹` are independent).
-/

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon Module

local instance : NeZero (2 : F7) := ⟨by decide⟩

local instance : Invertible (2 : F7) := ⟨4, by decide, by decide⟩

/-! ### Zero counts of quadratic forms on `F7^n` via diagonalisation -/

section quad

variable {V : Type*} [AddCommGroup V] [Module F7 V] [FiniteDimensional F7 V]

/-- Diagonalisation: a quadratic form `R` is isometric to `Σ wᵢ xᵢ²`; its zero count is
`wzeros w` and its polar radical has `7 ^ nzero w` elements. -/
theorem exists_diag (R : QuadraticForm F7 V) :
    ∃ (n : ℕ) (w : Fin n → F7), n = finrank F7 V ∧
      Nat.card {v : V // R v = 0} = wzeros w ∧
      Nat.card {v : V // ∀ u, QuadraticMap.polar R v u = 0} = 7 ^ nzero w := by
  obtain ⟨w, ⟨e⟩⟩ := QuadraticForm.equivalent_weightedSumSquares R
  have he : ∀ u, ∑ i, w i * e u i ^ 2 = R u := by
    intro u
    have := e.map_app u
    simp only [QuadraticMap.weightedSumSquares_apply, smul_eq_mul] at this
    rw [← this]
    simp [sq]
  have hB : ∀ u z : V, QuadraticMap.polar R u z = ∑ i, 2 * w i * e u i * e z i := by
    intro u z
    rw [QuadraticMap.polar, ← he, ← he, ← he, map_add, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.add_apply]
    ring
  refine ⟨_, w, rfl, ?_, ?_⟩
  · rw [wzeros, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr <| e.toLinearEquiv.toEquiv.subtypeEquiv fun u => by
      rw [← he u]
      rfl
  · rw [← card_diag_rad, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr <| e.toLinearEquiv.toEquiv.subtypeEquiv fun u => ?_
    rw [← diag_rad]
    refine ⟨fun h v' => ?_, fun h z => ?_⟩
    · obtain ⟨z, rfl⟩ := e.surjective v'
      exact (hB u z).symm.trans (h z)
    · exact (hB u z).trans (h _)

/-- Zero count of a quadratic form on a 7-dimensional space over `F7` in terms of the size `7^k`
of the radical of its polar form. -/
theorem quad_zeros_good (R : QuadraticForm F7 V) (hV : finrank F7 V = 7) {k : ℕ}
    (hk : Nat.card {v : V // ∀ u, QuadraticMap.polar R v u = 0} = 7 ^ k) :
    good7 k (Nat.card {v : V // R v = 0}) := by
  obtain ⟨n, w, hn, h1, h2⟩ := exists_diag R
  rw [hV] at hn
  subst hn
  rw [hk] at h2
  have h3 : nzero w = k := Nat.pow_right_injective (by norm_num : 2 ≤ 7) h2.symm
  rw [h1, ← h3]
  exact wzeros7 w

/-- Real form of `good7`: at most `7^6 + 6 · 7^((5+k)/2)` zeros. -/
theorem good7_real {k Z : ℕ} (h : good7 k Z) :
    (Z : ℝ) ≤ 7 ^ 6 + 6 * (7 : ℝ) ^ (((5 : ℝ) + k) / 2) := by
  unfold good7 at h
  split_ifs at h with hk
  · subst h
    have : (0 : ℝ) ≤ 6 * (7 : ℝ) ^ (((5 : ℝ) + k) / 2) := by positivity
    push_cast
    linarith
  · have hd : 2 ∣ 5 + k := by omega
    have hc : (((5 + k) / 2 : ℕ) : ℝ) = ((5 : ℝ) + k) / 2 := by
      rw [Nat.cast_div hd (by norm_num)]
      push_cast
      ring
    rw [← hc, Real.rpow_natCast]
    exact_mod_cast h

end quad

/-! ### The forms `R_c = F - c Q` -/

section Rc

variable (T : V7 F7 ≃ₗ[F7] V7 F7)

/-- `S_c = T + T⁻¹ - c`. -/
def Sc (c : F7) : V7 F7 →ₗ[F7] V7 F7 := T.toLinearMap + T.symm.toLinearMap - c • LinearMap.id

/-- `d_c = dim ker (T + T⁻¹ - c)`. -/
noncomputable def dk (c : F7) : ℕ := finrank F7 (LinearMap.ker (Sc T c))

/-- `R_c v = Bf v (T v) - c · Qf v` as a quadratic form. -/
def RcQ (c : F7) : QuadraticForm F7 (V7 F7) :=
  LinearMap.BilinMap.toQuadraticMap ((BfForm F7).compl₂ T.toLinearMap) - c • QfQ

theorem RcQ_apply (c : F7) (v : V7 F7) : RcQ T c v = Bf v (T v) - c * Qf v := by
  simp [RcQ, QfQ_apply]

variable {T}

theorem Bf_isom (hT : ∀ v, Qf (T v) = Qf v) (x y : V7 F7) : Bf (T x) (T y) = Bf x y := by
  have h1 := hT (x + y)
  rw [map_add, Qf_add, Qf_add, hT, hT] at h1
  linear_combination h1

theorem Bf_add_left (x y z : V7 F7) : Bf (x + y) z = Bf x z + Bf y z := by
  simp only [Bf, Pi.add_apply]; ring

theorem Bf_add_right (x y z : V7 F7) : Bf x (y + z) = Bf x y + Bf x z := by
  simp only [Bf, Pi.add_apply]; ring

theorem Bf_sub_right (x y z : V7 F7) : Bf x (y - z) = Bf x y - Bf x z := by
  simp only [Bf, Pi.sub_apply]; ring

theorem Bf_smul_right7 (x y : V7 F7) (c : F7) : Bf x (c • y) = c * Bf x y := by
  simp only [Bf, Pi.smul_apply, smul_eq_mul]; ring

theorem RcQ_polar (hT : ∀ v, Qf (T v) = Qf v) (c : F7) (v u : V7 F7) :
    QuadraticMap.polar (RcQ T c) v u = Bf v (Sc T c u) := by
  have h1 : Bf u (T v) = Bf v (T.symm u) := by
    conv_lhs => rw [← T.apply_symm_apply u]
    rw [Bf_isom hT, Bf_comm]
  rw [QuadraticMap.polar, RcQ_apply, RcQ_apply, RcQ_apply, map_add, Qf_add, Bf_add_left,
    Bf_add_right, Bf_add_right]
  simp only [Sc, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearEquiv.coe_coe, Bf_add_right, Bf_sub_right, Bf_smul_right7]
  rw [h1]
  ring

theorem card_rad_RcQ (hT : ∀ v, Qf (T v) = Qf v) (c : F7) :
    Nat.card {v : V7 F7 // ∀ u, QuadraticMap.polar (RcQ T c) v u = 0} = 7 ^ dk T c := by
  have : {v : V7 F7 // ∀ u, QuadraticMap.polar (RcQ T c) v u = 0} =
      {v : V7 F7 // v ∈ LinearMap.ker (Sc T c)} := by
    congr 1
    ext v
    rw [LinearMap.mem_ker]
    constructor
    · intro h
      refine (BfForm_nondegenerate (F := F7)).1 _ fun u => ?_
      rw [BfForm_apply, Bf_comm, ← RcQ_polar hT, QuadraticMap.polar_comm]
      exact h u
    · intro h u
      rw [QuadraticMap.polar_comm, RcQ_polar hT, h, Bf_comm]
      simp [Bf]
  rw [this, dk, Module.natCard_eq_pow_finrank (K := F7), Nat.card_zmod]

end Rc

/-! ### Counting and the final bound -/

section count

variable {T : V7 F7 ≃ₗ[F7] V7 F7}

/-- `Σ_c #{R_c = 0} = 7 · #{Qf = 0, F = 0} + #{Qf ≠ 0}`. -/
theorem sum_card_Rc (T : V7 F7 ≃ₗ[F7] V7 F7) :
    ∑ c : F7, (Finset.univ.filter fun v : V7 F7 => RcQ T c v = 0).card =
      7 * (Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0).card +
        (Finset.univ.filter fun v : V7 F7 => ¬Qf v = 0).card := by
  simp only [Finset.card_filter, RcQ_apply]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hQ : Qf v = 0
  · by_cases hF : Bf v (T v) = 0 <;> simp [hQ, hF]
  · have h : ∀ c : F7, (Bf v (T v) - c * Qf v = 0) ↔ (c = Bf v (T v) / Qf v) := fun c => by
      rw [sub_eq_zero, eq_div_iff hQ, eq_comm]
    simp only [h, hQ, false_and, if_false, mul_zero, not_false_eq_true, if_true, zero_add]
    simp

theorem card_V7 : Fintype.card (V7 F7) = 7 ^ 7 := by
  rw [Fintype.card_fun, ZMod.card, Fintype.card_fin]

theorem card_Qf_zero : Fintype.card {x : V7 F7 // Qf x = 0} = 7 ^ 6 := by
  have h2 := card_zeros_Qf (F := F7)
  rw [ZMod.card] at h2
  exact h2

theorem card_Qf_ne_zero :
    (Finset.univ.filter fun v : V7 F7 => ¬Qf v = 0).card = 7 ^ 7 - 7 ^ 6 := by
  classical
  have h2 : (Finset.univ.filter fun v : V7 F7 => Qf v = 0).card = 7 ^ 6 := by
    rw [← Fintype.card_subtype]; exact card_Qf_zero
  rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
    card_V7, h2]

/-- The number of zeros of `R_c`: at most `7^6 + 6 · 7^((5 + d_c)/2)`. -/
theorem card_Rc_le (hT : ∀ v, Qf (T v) = Qf v) (c : F7) :
    ((Finset.univ.filter fun v : V7 F7 => RcQ T c v = 0).card : ℝ) ≤
      7 ^ 6 + 6 * (7 : ℝ) ^ (((5 : ℝ) + dk T c) / 2) := by
  apply good7_real
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact quad_zeros_good (RcQ T c) finrank_V7 (card_rad_RcQ hT c)

/-- **Lemma 4.4 of OMEGA_REPAIR.md for `q = 7`.** For an isometry `T` of `(F7^7, Qf)`,
`#{v : Qf v = 0, Bf v (T v) = 0} ≤ 7^5 + 6 Σ_c 7^((3 + d_c)/2)` with `d_c = dim ker (T + T⁻¹ - c)`. -/
theorem count_QF_le (T : V7 F7 ≃ₗ[F7] V7 F7) (hT : ∀ v, Qf (T v) = Qf v) :
    ((Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0).card : ℝ) ≤
      7 ^ 5 + 6 * ∑ c : F7, (7 : ℝ) ^ (((3 : ℝ) + dk T c) / 2) := by
  have hsum := sum_card_Rc T
  rw [card_Qf_ne_zero] at hsum
  have hsumR : (∑ c : F7, ((Finset.univ.filter fun v : V7 F7 => RcQ T c v = 0).card : ℝ)) =
      7 * ((Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0).card : ℝ) +
        (7 ^ 7 - 7 ^ 6) := by
    rw [← Nat.cast_sum, hsum]
    push_cast
    norm_num
  have hle := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => card_Rc_le hT c
  have h7 : ∀ c : F7, (7 : ℝ) ^ (((5 : ℝ) + dk T c) / 2) =
      7 * (7 : ℝ) ^ (((3 : ℝ) + dk T c) / 2) := fun c => by
    rw [show ((5 : ℝ) + dk T c) / 2 = 1 + ((3 : ℝ) + dk T c) / 2 by ring,
      Real.rpow_add (by norm_num), Real.rpow_one]
  simp only [h7, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul, ← Finset.mul_sum] at hle
  rw [hsumR] at hle
  push_cast at hle
  linarith

end count

/-! ### `Σ_c d_c ≤ 7` -/

theorem ker_Sc_eq (T : V7 F7 ≃ₗ[F7] V7 F7) (c : F7) :
    LinearMap.ker (Sc T c) =
      Module.End.eigenspace (T.toLinearMap + T.symm.toLinearMap : Module.End F7 (V7 F7)) c := by
  ext v
  simp [Module.End.mem_eigenspace_iff, Sc, sub_eq_zero]

/-- The kernels of `T + T⁻¹ - c` (`c ∈ F7`) are eigenspaces of one operator, hence independent, so
their dimensions add up to at most `7`. -/
theorem sum_dk_le (T : V7 F7 ≃ₗ[F7] V7 F7) : ∑ c : F7, dk T c ≤ 7 := by
  set f : Module.End F7 (V7 F7) := T.toLinearMap + T.symm.toLinearMap
  have hind := Module.End.eigenspaces_iSupIndep f
  let L : (∀ c : F7, f.eigenspace c) →ₗ[F7] V7 F7 :=
    ∑ c : F7, (f.eigenspace c).subtype ∘ₗ LinearMap.proj c
  have hL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    have hg' : ∑ c : F7, (g c : V7 F7) = 0 := by simpa [L] using hg
    have := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero _).1 hind Finset.univ
      (fun c => (g c : V7 F7)) (fun c _ => (g c).2) hg'
    funext c
    exact Subtype.ext (this c (Finset.mem_univ c))
  have h := LinearMap.finrank_le_finrank_of_injective hL
  rw [Module.finrank_pi_fintype, finrank_V7] at h
  calc ∑ c : F7, dk T c = ∑ c : F7, finrank F7 (f.eigenspace c) :=
        Finset.sum_congr rfl fun c _ => by rw [dk, ker_Sc_eq]
    _ ≤ 7 := h

end BipartiteDD.LeanMaxx.Omega45b
