import BipartiteDD.ASq.Lines
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-! ASq, part 3: Theorem A. Two elliptic quadrics form a weighted 2-ovoid of AS(q).

With `ε` a non-square, `N(b, c) = b² - ε c²`, and `Q_c = {(c N(w), w) : w ∈ F²}`, the weight
`wt x = [x ∈ Q_c1] + [x ∈ Q_c2]` has total weight `2` on every line when `c1 c2 = 1 / (4 ε)`.

On a fibre, `Q_c` has one point, so the total is `1 + 1`. On a coset `g Z_d`, the points of `Q_c`
are the roots of a quadratic in the parameter `t`. The number of roots is `1 + χ(Δ_c)`, with `χ` the
quadratic character and `Δ_c` the discriminant. The identity `c2 Δ_c1 = c1 Δ_c2` together with
`χ(c1 c2) = χ(ε) = -1` makes `χ(Δ_c1) + χ(Δ_c2) = 0`. -/

namespace BipartiteDD.ASq

open scoped Classical

variable {F : Type*} [Field F]

/-- The norm form `N(b, c) = b ^ 2 - ε c ^ 2`. -/
def nrm (ε : F) (w : F × F) : F := w.1 ^ 2 - ε * w.2 ^ 2

/-- The quadric `Q_c = {(c N(w), w) : w ∈ F²}`. -/
def Qset (ε c : F) : Set (F × F × F) := {x | x.1 = c * nrm ε x.2}

/-- The weight `[x ∈ Q_c1] + [x ∈ Q_c2]`. -/
noncomputable def wt (ε c1 c2 : F) (x : F × F × F) : ℕ :=
  (if x ∈ Qset ε c1 then 1 else 0) + (if x ∈ Qset ε c2 then 1 else 0)

theorem two_ne_zero_of_ringChar (hF : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  exact hF (((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one)

theorem nrm_ne_zero {ε : F} (hε : ¬IsSquare ε) {d : F × F} (hd : d ≠ 0) : nrm ε d ≠ 0 := by
  intro h
  by_cases h2 : d.2 = 0
  · apply hd
    have h1 : d.1 = 0 := by
      have h3 : d.1 ^ 2 = 0 := by
        rw [nrm, h2] at h
        linear_combination h
      exact pow_eq_zero_iff two_ne_zero |>.mp h3
    exact Prod.ext h1 h2
  · have h' : d.1 ^ 2 - ε * d.2 ^ 2 = 0 := h
    exact hε ⟨d.1 / d.2, by field_simp; linear_combination -h'⟩

omit [Field F] in
/-- Summing a function over a line reindexes it along the parametrisation. -/
theorem sum_line [Fintype F] {ℓ : Set (F × F × F)} {f : F → F × F × F} (hf : Function.Injective f)
    (hℓ : ℓ = Set.range f) (g : F × F × F → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ ℓ), g x = ∑ μ : F, g (f μ) := by
  have h : Finset.univ.filter (fun x => x ∈ ℓ) = Finset.univ.image f := by
    ext x
    simp [hℓ]
  rw [h, Finset.sum_image (fun a _ b _ hab => hf hab)]

/-- The number of roots of `A λ² + B λ + C` is `1 + χ(B² - 4AC)` when `A ≠ 0`. -/
theorem root_count [Fintype F] (hF : ringChar F ≠ 2) {A B C : F} (hA : A ≠ 0) :
    ((∑ l : F, if A * l ^ 2 + B * l + C = 0 then (1 : ℕ) else 0 : ℕ) : ℤ) =
      1 + quadraticChar F (B ^ 2 - 4 * A * C) := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_ringChar hF
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4A : 4 * A ≠ 0 := mul_ne_zero h4 hA
  have hA2 : 2 * A ≠ 0 := mul_ne_zero h2 hA
  have hbij : Function.Bijective (fun l : F => 2 * A * l + B) := by
    constructor
    · intro a b hab
      exact mul_left_cancel₀ hA2 (add_right_cancel hab)
    · intro y
      exact ⟨(y - B) / (2 * A), by field_simp; ring⟩
  have hpt : ∀ l : F, (if A * l ^ 2 + B * l + C = 0 then (1 : ℕ) else 0) =
      (if (2 * A * l + B) ^ 2 = B ^ 2 - 4 * A * C then 1 else 0) := by
    intro l
    have key : A * l ^ 2 + B * l + C = 0 ↔ (2 * A * l + B) ^ 2 = B ^ 2 - 4 * A * C := by
      constructor
      · intro h
        linear_combination (4 * A) * h
      · intro h
        have h' : (4 * A) * (A * l ^ 2 + B * l + C) = 0 := by linear_combination h
        exact (mul_eq_zero.mp h').resolve_left h4A
    simp only [key]
  have hsum : (∑ l : F, if A * l ^ 2 + B * l + C = 0 then (1 : ℕ) else 0) =
      ∑ y : F, if y ^ 2 = B ^ 2 - 4 * A * C then (1 : ℕ) else 0 :=
    Fintype.sum_bijective _ hbij _ _ hpt
  have hcard := quadraticChar_card_sqrts hF (B ^ 2 - 4 * A * C)
  rw [hsum, Finset.sum_boole]
  simp only [Set.toFinset_ofPred] at hcard
  rw [add_comm, ← hcard]
  norm_cast

/-- If `c2 Δ1 = c1 Δ2` with `χ(c1 c2) = χ(ε) = -1`, then `χ(Δ1) + χ(Δ2) = 0`. -/
theorem chi_pair [Fintype F] (hF : ringChar F ≠ 2) {ε c1 c2 : F} (hε : ¬IsSquare ε)
    (h4 : 4 * ε * (c1 * c2) = 1) {Δ1 Δ2 : F} (hΔ : c2 * Δ1 = c1 * Δ2) :
    quadraticChar F Δ1 + quadraticChar F Δ2 = 0 := by
  have h2 := two_ne_zero_of_ringChar hF
  have hc1 : c1 ≠ 0 := by
    rintro rfl
    simp at h4
  have hχ4 : quadraticChar F 4 = 1 := by
    rw [show (4 : F) = 2 * 2 by norm_num, map_mul, ← sq]
    exact quadraticChar_sq_one h2
  have hχε : quadraticChar F ε = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hε
  have hprod : quadraticChar F c1 * quadraticChar F c2 = -1 := by
    have h1 : quadraticChar F (4 * ε * (c1 * c2)) = 1 := by rw [h4, map_one]
    simp only [map_mul, hχ4, hχε] at h1
    linarith
  have hsq1 : quadraticChar F c1 ^ 2 = 1 := quadraticChar_sq_one hc1
  have hmul : quadraticChar F Δ1 * quadraticChar F c2 =
      quadraticChar F c1 * quadraticChar F Δ2 := by
    have := congrArg (quadraticChar F) hΔ
    simp only [map_mul] at this
    linear_combination this
  linear_combination (-quadraticChar F c1) * hmul + quadraticChar F Δ1 * hprod -
    quadraticChar F Δ2 * hsq1

/-- The two root counts add up to `2`, given the discriminant relation. -/
theorem two_root_sum [Fintype F] (hF : ringChar F ≠ 2) {ε c1 c2 : F} (hε : ¬IsSquare ε)
    (h4 : 4 * ε * (c1 * c2) = 1) {A1 B1 C1 A2 B2 C2 : F} (hA1 : A1 ≠ 0) (hA2 : A2 ≠ 0)
    (hΔ : c2 * (B1 ^ 2 - 4 * A1 * C1) = c1 * (B2 ^ 2 - 4 * A2 * C2)) :
    (∑ t : F, if A1 * t ^ 2 + B1 * t + C1 = 0 then (1 : ℕ) else 0) +
      (∑ t : F, if A2 * t ^ 2 + B2 * t + C2 = 0 then (1 : ℕ) else 0) = 2 := by
  have r1 := root_count hF hA1 (B := B1) (C := C1)
  have r2 := root_count hF hA2 (B := B2) (C := C2)
  have hχ := chi_pair hF hε h4 hΔ
  have : ((∑ t : F, if A1 * t ^ 2 + B1 * t + C1 = 0 then (1 : ℕ) else 0 : ℕ) : ℤ) +
      ((∑ t : F, if A2 * t ^ 2 + B2 * t + C2 = 0 then (1 : ℕ) else 0 : ℕ) : ℤ) = 2 := by
    rw [r1, r2]
    linarith
  exact_mod_cast this

/-- The membership of a point of a coset in `Q_c` is a quadratic condition on the parameter. -/
theorem mem_Qset_iff (ε c : F) (g : F × F × F) (d : F × F) (t : F) :
    (g.1 + t * det g.2 d, (g.2.1 + t * d.1, g.2.2 + t * d.2)) ∈ Qset ε c ↔
      c * nrm ε d * t ^ 2 + (c * (2 * (g.2.1 * d.1 - ε * g.2.2 * d.2)) - det g.2 d) * t +
        (c * nrm ε g.2 - g.1) = 0 := by
  simp only [Qset, nrm, det, Set.mem_ofPred_eq]
  constructor <;> intro h <;> linear_combination -h

/-- The discriminants of the two quadrics along a coset satisfy `c2 Δ1 = c1 Δ2`. -/
theorem disc_rel {ε c1 c2 : F} (h4 : 4 * ε * (c1 * c2) = 1) (g : F × F × F) (d : F × F) :
    c2 * ((c1 * (2 * (g.2.1 * d.1 - ε * g.2.2 * d.2)) - det g.2 d) ^ 2 -
        4 * (c1 * nrm ε d) * (c1 * nrm ε g.2 - g.1)) =
      c1 * ((c2 * (2 * (g.2.1 * d.1 - ε * g.2.2 * d.2)) - det g.2 d) ^ 2 -
        4 * (c2 * nrm ε d) * (c2 * nrm ε g.2 - g.1)) := by
  simp only [nrm, det]
  linear_combination (c1 - c2) * (g.2.1 * d.2 - g.2.2 * d.1) ^ 2 * h4

/-- Weight of a coset: the parametrised line `lineA g d` carries total weight `2`. -/
theorem lineA_weight [Fintype F] (hF : ringChar F ≠ 2) {ε c1 c2 : F} (hε : ¬IsSquare ε)
    (h4 : 4 * ε * (c1 * c2) = 1) (g : F × F × F) {d : F × F} (hd : d ≠ 0) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ lineA g d), wt ε c1 c2 x = 2 := by
  have hc1 : c1 ≠ 0 := by
    rintro rfl
    simp at h4
  have hc2 : c2 ≠ 0 := by
    rintro rfl
    simp at h4
  have hinj : Function.Injective
      (fun t : F => (g.1 + t * det g.2 d, (g.2.1 + t * d.1, g.2.2 + t * d.2))) := by
    intro t t' h
    have h2 := congrArg (fun x : F × F × F => x.2) h
    have h3 := congrArg (fun x : F × F => x.1) h2
    have h4' := congrArg (fun x : F × F => x.2) h2
    simp only at h3 h4'
    rcases eq_or_ne d.1 0 with h1 | h1
    · have h5 : d.2 ≠ 0 := fun h5 => hd (Prod.ext h1 h5)
      have h6 : t * d.2 = t' * d.2 := by linear_combination h4'
      exact mul_right_cancel₀ h5 h6
    · have h6 : t * d.1 = t' * d.1 := by linear_combination h3
      exact mul_right_cancel₀ h1 h6
  rw [sum_line (ℓ := lineA g d) hinj rfl]
  simp only [wt, Finset.sum_add_distrib, mem_Qset_iff]
  refine two_root_sum hF hε h4 (mul_ne_zero hc1 (nrm_ne_zero hε hd))
    (mul_ne_zero hc2 (nrm_ne_zero hε hd)) ?_
  exact disc_rel h4 g d

omit [Field F] in
/-- The indicator of `k` sums to one over `F`. -/
theorem sum_ite_eq_k [Fintype F] (k : F) : ∑ x : F, (if x = k then (1 : ℕ) else 0) = 1 := by
  simp

/-- A fibre meets `Q_c` in exactly one point. -/
theorem sum_ite_mem_fib [Fintype F] (ε c : F) (w : F × F) :
    ∑ μ : F, (if (μ, w) ∈ Qset ε c then (1 : ℕ) else 0) = 1 := by
  have h : ∀ μ : F, (if (μ, w) ∈ Qset ε c then (1 : ℕ) else 0) =
      if μ = c * nrm ε w then 1 else 0 :=
    fun μ => if_congr Iff.rfl rfl rfl
  simp only [h]
  exact sum_ite_eq_k _

/-- A fibre carries total weight `2`. -/
theorem fib_weight (ε c1 c2 : F) [Fintype F] (w : F × F) :
    ∑ μ : F, wt ε c1 c2 (μ, w) = 2 := by
  simp only [wt, Finset.sum_add_distrib, sum_ite_mem_fib]

/-- Statement 2: the weight `wt` is a weighted 2-ovoid of AS(q). -/
theorem weighted_two_ovoid [Fintype F] (hF : ringChar F ≠ 2) {ε : F} (hε : ¬IsSquare ε)
    {c1 c2 : F} (hc : c1 * c2 = 1 / (4 * ε)) (ℓ : Line F) :
    ∑ x ∈ Finset.univ.filter (fun x => x ∈ ℓ), wt ε c1 c2 x = 2 := by
  have hε0 : ε ≠ 0 := fun h => hε ⟨0, by simp [h]⟩
  have h4ε : 4 * ε ≠ 0 := mul_ne_zero (by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero (two_ne_zero_of_ringChar hF) (two_ne_zero_of_ringChar hF)) hε0
  have h4 : 4 * ε * (c1 * c2) = 1 := by
    rw [hc]
    exact mul_one_div_cancel h4ε
  rcases ℓ.carrier_cases with ⟨g, d, hd, hl⟩ | ⟨w, hl⟩
  · show ∑ x ∈ Finset.univ.filter (fun x => x ∈ ℓ.carrier), wt ε c1 c2 x = 2
    rw [hl]
    exact lineA_weight hF hε h4 g hd
  · show ∑ x ∈ Finset.univ.filter (fun x => x ∈ ℓ.carrier), wt ε c1 c2 x = 2
    rw [hl]
    have hinj : Function.Injective (fun μ : F => (μ, w)) := fun a b h => by
      simpa using congrArg Prod.fst h
    rw [sum_line (ℓ := fib w) hinj rfl]
    exact fib_weight ε c1 c2 w

/-- The total weight of `Q_c` is `q²`. -/
theorem sum_Qset [Fintype F] (ε c : F) :
    ∑ x : F × F × F, (if x ∈ Qset ε c then (1 : ℕ) else 0) = Fintype.card F ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp only [sum_ite_mem_fib, Finset.sum_const, Finset.card_univ, Fintype.card_prod, smul_eq_mul,
    mul_one, sq]

/-- The total weight of the points is `2 q²`. -/
theorem sum_wt [Fintype F] (ε c1 c2 : F) :
    ∑ x : F × F × F, wt ε c1 c2 x = 2 * Fintype.card F ^ 2 := by
  simp only [wt, Finset.sum_add_distrib, sum_Qset]
  ring

end BipartiteDD.ASq
