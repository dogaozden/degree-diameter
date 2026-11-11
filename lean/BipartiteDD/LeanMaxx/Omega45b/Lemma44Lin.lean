import BipartiteDD.LeanMaxx.Omega45b.CharSum
import BipartiteDD.LeanMaxx.Omega45b.PerpQuadric
import BipartiteDD.LeanMaxx.Omega45b.Points

/-!
# Lemma 4.4 from the linear structure of collineations

`CharSum.lean` proves, for every linear isometry `T` of `(F7^7, Qf)`,
`#{v : Qf v = 0 ∧ Bf v (T v) = 0} ≤ 7^5 + 6 Σ_c 7^((3 + d_c)/2)` with `d_c = dim ker (T + T⁻¹ - c)` and
`Σ_c d_c ≤ 7`. Here the numerical step of the note is added (`d_c ≤ 4` and `Σ d_c ≤ 7` give
`Σ_c 7^((3+d_c)/2) < 1344`, whence `|Perp| ≤ 4144`) and the count of vectors is turned into the count of points.

The group-theoretic input of the note is the single explicit hypothesis `LinearLift`:
a collineation of `H(7)` with no fixed point is induced by a linear isometry `T` of `(F7^7, Qf)`
(`Aut H(7) = G₂(7) ≤ SO(7,7)`; the lift is unique, because `q` is prime) with `d_c ≤ 4` for every `c`
(the eigenvalues of an element of `G₂` on the 7-dimensional module are `1, x, y, xy` and inverses, so an
eigenvalue of multiplicity three needs `μ³ = 1`, which lies in `F7` as `3 ∣ 6`; then (i)–(iii) of the note).
`lemma44_of_linearLift : LinearLift → Lemma44` is proved here.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45

/-! ### The numerical step -/

theorem rp (d : ℕ) : (7 : ℝ) ^ (((3 : ℝ) + d) / 2) = Real.sqrt 7 ^ (3 + d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1
  push_cast
  ring

theorem sqrt7_sq : Real.sqrt 7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)

theorem sqrt7_le : Real.sqrt 7 ≤ 2.64576 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

theorem sqrt7_nonneg : 0 ≤ Real.sqrt 7 := Real.sqrt_nonneg _

theorem pow_vals :
    Real.sqrt 7 ^ 3 = 7 * Real.sqrt 7 ∧ Real.sqrt 7 ^ 4 = 49 ∧ Real.sqrt 7 ^ 5 = 49 * Real.sqrt 7 ∧
      Real.sqrt 7 ^ 6 = 343 ∧ Real.sqrt 7 ^ 7 = 343 * Real.sqrt 7 := by
  have h2 := sqrt7_sq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc Real.sqrt 7 ^ 3 = Real.sqrt 7 ^ 2 * Real.sqrt 7 := by ring
      _ = 7 * Real.sqrt 7 := by rw [h2]
  · calc Real.sqrt 7 ^ 4 = (Real.sqrt 7 ^ 2) ^ 2 := by ring
      _ = 49 := by rw [h2]; norm_num
  · calc Real.sqrt 7 ^ 5 = (Real.sqrt 7 ^ 2) ^ 2 * Real.sqrt 7 := by ring
      _ = 49 * Real.sqrt 7 := by rw [h2]; norm_num
  · calc Real.sqrt 7 ^ 6 = (Real.sqrt 7 ^ 2) ^ 3 := by ring
      _ = 343 := by rw [h2]; norm_num
  · calc Real.sqrt 7 ^ 7 = (Real.sqrt 7 ^ 2) ^ 3 * Real.sqrt 7 := by ring
      _ = 343 * Real.sqrt 7 := by rw [h2]; norm_num

theorem pow_bound (d : ℕ) (hd : d ≤ 3) : Real.sqrt 7 ^ (3 + d) ≤ 18.53 + 108.3 * d := by
  obtain ⟨e3, e4, e5, e6, e7⟩ := pow_vals
  have hle := sqrt7_le
  interval_cases d
  · norm_num; rw [e3]; linarith
  · norm_num; rw [e4]; norm_num
  · norm_num; rw [e5]; linarith
  · norm_num; rw [e6]; norm_num

theorem pow_four : Real.sqrt 7 ^ (3 + 4) ≤ 907.5 := by
  obtain ⟨e3, e4, e5, e6, e7⟩ := pow_vals
  have hle := sqrt7_le
  norm_num; rw [e7]; linarith

/-- `d_c ≤ 4`, `Σ d_c ≤ 7` give `Σ_c 7^((3+d_c)/2) < 1344`. -/
theorem sum_rpow_lt (d : F7 → ℕ) (hd : ∀ c, d c ≤ 4) (hs : ∑ c, d c ≤ 7) :
    ∑ c : F7, (7 : ℝ) ^ (((3 : ℝ) + d c) / 2) < 1344 := by
  simp only [rp]
  by_cases h4 : ∃ c0, d c0 = 4
  · obtain ⟨c0, hc0⟩ := h4
    have hsplit := Finset.add_sum_erase Finset.univ (fun c => d c) (Finset.mem_univ c0)
    have hsplitR := Finset.add_sum_erase Finset.univ (fun c => Real.sqrt 7 ^ (3 + d c)) (Finset.mem_univ c0)
    have hrest : ∑ c ∈ Finset.univ.erase c0, d c ≤ 3 := by omega
    have hle3 : ∀ c ∈ Finset.univ.erase c0, d c ≤ 3 := fun c hc =>
      le_trans (Finset.single_le_sum (f := fun c => d c) (fun _ _ => Nat.zero_le _) hc) hrest
    have hb : ∀ c ∈ Finset.univ.erase c0, Real.sqrt 7 ^ (3 + d c) ≤ 18.53 + 108.3 * (d c : ℝ) :=
      fun c hc => pow_bound (d c) (hle3 c hc)
    have hsumb := Finset.sum_le_sum hb
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at hsumb
    have hcard : (Finset.univ.erase c0).card = 6 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
    have hrestR : ((∑ c ∈ Finset.univ.erase c0, d c : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hrest
    push_cast at hrestR
    rw [hcard] at hsumb
    simp only [nsmul_eq_mul] at hsumb
    push_cast at hsumb
    have h7 := pow_four
    rw [hc0] at hsplitR
    have h8 : ∑ i ∈ Finset.univ.erase c0, Real.sqrt 7 ^ (3 + d i) ≤ 436.1 := by
      have h9 : (108.3 : ℝ) * ∑ i ∈ Finset.univ.erase c0, ((d i : ℕ) : ℝ) ≤ 108.3 * 3 :=
        mul_le_mul_of_nonneg_left hrestR (by norm_num)
      refine hsumb.trans ?_
      norm_num at h9 ⊢
      linarith
    generalize Real.sqrt 7 ^ (3 + 4) = X at h7 hsplitR
    rw [← hsplitR]
    linarith
  · push Not at h4
    have hle3 : ∀ c, d c ≤ 3 := fun c => by have := hd c; have := h4 c; omega
    have hb : ∀ c ∈ (Finset.univ : Finset F7), Real.sqrt 7 ^ (3 + d c) ≤ 18.53 + 108.3 * (d c : ℝ) :=
      fun c _ => pow_bound (d c) (hle3 c)
    have hsumb := Finset.sum_le_sum hb
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum] at hsumb
    have hsR : ((∑ c, d c : ℕ) : ℝ) ≤ 7 := by exact_mod_cast hs
    push_cast at hsR
    simp only [Finset.card_univ, ZMod.card, nsmul_eq_mul] at hsumb
    push_cast at hsumb
    nlinarith

/-! ### From vectors to points -/

/-- The group-theoretic input of Lemma 4.4. -/
def LinearLift : Prop :=
  ∀ h : autSub G7 klass, (∀ p : SPt F7, (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl p) ≠ Sum.inl p) →
    ∃ T : V7 F7 ≃ₗ[F7] V7 F7, (∀ v, Qf (T v) = Qf v) ∧
      (∀ p : SPt F7, ∃ p' : SPt F7, ∃ c : F7, c ≠ 0 ∧
        (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl p) = Sum.inl p' ∧ p'.1.rep = c • T p.1.rep) ∧
      ∀ c : F7, dk T c ≤ 4

theorem Bf_T_smul (T : V7 F7 ≃ₗ[F7] V7 F7) (c : F7) (v : V7 F7) :
    Bf (c • v) (T (c • v)) = c ^ 2 * Bf v (T v) := by
  rw [map_smul]
  simp only [Bf, Pi.smul_apply, smul_eq_mul]
  ring

/-- Number of points `s` with `Bf s (T s) = 0`: `6 · #points + 1 = #{v : Qf v = 0 ∧ Bf v (T v) = 0}`. -/
theorem card_pts_perp (T : V7 F7 ≃ₗ[F7] V7 F7) :
    6 * (Finset.univ.filter fun s : SPt F7 => Bf s.1.rep (T s.1.rep) = 0).card + 1 =
      (Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0).card := by
  classical
  have h6 := card_pts_mul (fun v : V7 F7 => Bf v (T v) = 0) (fun c v hc => by
    rw [Bf_T_smul]
    constructor
    · intro h
      exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero 2 hc)
    · intro h
      rw [h, mul_zero])
  rw [h6]
  have hsub : (Finset.univ.filter fun v : V7 F7 => v ≠ 0 ∧ Qf v = 0 ∧ Bf v (T v) = 0) =
      (Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0).erase 0 := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
  have h0 : (0 : V7 F7) ∈ (Finset.univ.filter fun v : V7 F7 => Qf v = 0 ∧ Bf v (T v) = 0) := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simp [Qf], by simp [Bf]⟩
  rw [hsub, Finset.card_erase_add_one h0]

/-- **Lemma 4.4 for `H(7)` from the linear structure** (`LinearLift`). -/
theorem lemma44_of_linearLift (hL : LinearLift) : Lemma44 := by
  intro h hfix
  obtain ⟨T, hT, hind, hdk⟩ := hL h hfix
  -- the points moved to a point at distance ≤ 4 are the points with `Bf s (T s) = 0`
  have hcard : Nat.card {s : SPt F7 // ∃ p : SPt F7, (h : Equiv.Perm (SPt F7 ⊕ HLine F7)) (Sum.inl s) = Sum.inl p ∧
      Bf s.1.rep p.1.rep = 0} = (Finset.univ.filter fun s : SPt F7 => Bf s.1.rep (T s.1.rep) = 0).card := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    obtain ⟨p', c, hc, hp, hrep⟩ := hind s
    constructor
    · rintro ⟨p, hp2, hb⟩
      rw [hp] at hp2
      have := Sum.inl_injective hp2
      subst this
      rw [hrep, Bf_smul_right] at hb
      exact (mul_eq_zero.1 hb).resolve_left hc
    · intro hb
      refine ⟨p', hp, ?_⟩
      rw [hrep, Bf_smul_right, hb, mul_zero]
  rw [hcard]
  set P := (Finset.univ.filter fun s : SPt F7 => Bf s.1.rep (T s.1.rep) = 0).card with hP
  have hN := card_pts_perp T
  rw [← hP] at hN
  have hcs := count_QF_le T hT
  have hsum := sum_dk_le T
  have hS := sum_rpow_lt (fun c => dk T c) hdk hsum
  by_contra hlt
  push Not at hlt
  have h1 : ((6 * P + 1 : ℕ) : ℝ) ≥ 24871 := by
    have : 6 * P + 1 ≥ 24871 := by omega
    exact_mod_cast this
  rw [hN] at h1
  linarith

/-- **Theorem 4.5 at `H(7)`, modulo `LinearLift` only** (the classification input: collineations of `H(7)` are
linear isometries, and a fixed-point-free one has `d_c ≤ 4`). Everything else (Lemma 4.3, the character-sum
bound, the final double count) is proved. -/
theorem omega45_H7_of_linearLift (hL : LinearLift) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7))
    (hμ : ∀ c u, klass (μ c u) = klass u) (hgeo : Geometric G7 klass μ) :
    (9 : ℕ∞) ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam :=
  omega45_H7_geometric (lemma44_of_linearLift hL) hα h2 typ ε₀ μ hμ hgeo

end BipartiteDD.LeanMaxx.Omega45b
