import BipartiteDD.SingerC.Classes
import BipartiteDD.SingerC.QuadCount

/-! Part (c) of Proposition C, first half: the class test as a trace condition, the quadratic
form in the two coordinates of a 2-dimensional subspace, and membership of its coefficients in `F`. -/

namespace BipartiteDD.SingerC

open Finset

namespace Setting

variable {K : Type*} [Field K] [Fintype K] {p : ℕ} [Fact p.Prime] [CharP K p]
variable (S : Setting K p)

/-- `ν_a = ω / h ^ a`. -/
def nu (a : ℕ) : K := S.ω * (S.h ^ a)⁻¹

theorem pow_q2_q2 (y : K) : (y ^ (S.q ^ 2)) ^ (S.q ^ 2) = y := by
  rw [← pow_mul, show S.q ^ 2 * S.q ^ 2 = S.q ^ 4 by ring, S.pow_card]

theorem tr2_omega (r : K) : S.tr2 (S.ω * r) = S.ω * (r - r ^ S.q) := by
  unfold tr2
  rw [mul_pow, S.ω_pow_q]
  ring

theorem tr2_mem_F {w : K} (hw : w ∈ S.L) : S.tr2 w ∈ S.F := by
  rw [mem_F]
  have hw2 : (w ^ S.q) ^ S.q = w := by
    rw [← pow_mul, ← pow_two]
    exact S.mem_L.mp hw
  unfold tr2
  rw [add_pow_q1, hw2, add_comm]

theorem nu_mem_L (a : ℕ) : S.nu a ∈ S.L :=
  S.L.mul_mem S.ω_mem_L (S.L.inv_mem (S.L.pow_mem S.h_mem_L a))

theorem norm_mem_L (x : K) : x ^ (S.q ^ 2 + 1) ∈ S.L := by
  rw [mem_L, ← pow_mul, show (S.q ^ 2 + 1) * S.q ^ 2 = S.q ^ 4 + S.q ^ 2 by ring, pow_add,
    S.pow_card, pow_succ x (S.q ^ 2), mul_comm]

theorem cross_mem_L (x y : K) : x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y ∈ S.L := by
  rw [mem_L, add_pow_q2, mul_pow, mul_pow, S.pow_q2_q2, S.pow_q2_q2, add_comm]

theorem ω_ne_zero : S.ω ≠ 0 := pow_ne_zero _ S.h_ne_zero

theorem h_pow_ne_zero (a : ℕ) : S.h ^ a ≠ 0 := pow_ne_zero _ S.h_ne_zero

/-- The coefficient of `s²` in `Tr(ν_a N(s x + t y))`. -/
def cA (a : ℕ) (x : K) : K := S.tr2 (S.nu a * x ^ (S.q ^ 2 + 1))

/-- The coefficient of `t²`. -/
def cC (a : ℕ) (y : K) : K := S.tr2 (S.nu a * y ^ (S.q ^ 2 + 1))

/-- The coefficient of `s t`. -/
def cB (a : ℕ) (x y : K) : K := S.tr2 (S.nu a * (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y))

/-- The discriminant of the quadratic form in `(s, t)`. -/
def dis (a : ℕ) (x y : K) : K := S.cB a x y ^ 2 - 4 * S.cA a x * S.cC a y

theorem cA_mem_F (a : ℕ) (x : K) : S.cA a x ∈ S.F :=
  S.tr2_mem_F (S.L.mul_mem (S.nu_mem_L a) (S.norm_mem_L x))

theorem cB_mem_F (a : ℕ) (x y : K) : S.cB a x y ∈ S.F :=
  S.tr2_mem_F (S.L.mul_mem (S.nu_mem_L a) (S.cross_mem_L x y))

theorem cC_mem_F (a : ℕ) (y : K) : S.cC a y ∈ S.F :=
  S.tr2_mem_F (S.L.mul_mem (S.nu_mem_L a) (S.norm_mem_L y))

/-- For `s, t ∈ F`: `N(s x + t y) = s² N(x) + s t (x ȳ + x̄ y) + t² N(y)`. -/
theorem norm_expand {s t : K} (hs : s ∈ S.F) (ht : t ∈ S.F) (x y : K) :
    (s * x + t * y) ^ (S.q ^ 2 + 1)
      = s ^ 2 * x ^ (S.q ^ 2 + 1) + s * t * (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y)
        + t ^ 2 * y ^ (S.q ^ 2 + 1) := by
  have hs2 : s ^ S.q ^ 2 = s := S.pow_q_pow_of_pow_q (S.mem_F.mp hs) 2
  have ht2 : t ^ S.q ^ 2 = t := S.pow_q_pow_of_pow_q (S.mem_F.mp ht) 2
  rw [pow_succ (s * x + t * y) (S.q ^ 2), add_pow_q2, mul_pow, mul_pow, hs2, ht2,
    pow_succ x (S.q ^ 2), pow_succ y (S.q ^ 2), pow_two s, pow_two t]
  ring

/-- Coefficients of a 2-dimensional form are compatible with the trace: `Tr(ν_a N(z)) = 0` is
the class test. -/
theorem inClass_iff_tr2 {a : ℕ} (ha : a < S.q + 1) {z : K} (hz : z ≠ 0) :
    S.InClass a z ↔ S.tr2 (S.nu a * z ^ (S.q ^ 2 + 1)) = 0 := by
  have hha : S.h ^ a ≠ 0 := S.h_pow_ne_zero a
  rw [S.inClass_iff ha hz]
  constructor
  · rintro ⟨c, hcF, hc0, hn⟩
    rw [hn]
    have h1 : S.nu a * (S.h ^ a * c) = S.ω * c := by
      unfold nu
      field_simp
    rw [h1, S.tr2_omega, S.mem_F.mp hcF, sub_self, mul_zero]
  · intro h0
    have hr : S.nu a * z ^ (S.q ^ 2 + 1) = S.ω * (z ^ (S.q ^ 2 + 1) * (S.h ^ a)⁻¹) := by
      unfold nu
      ring
    rw [hr, S.tr2_omega, mul_eq_zero] at h0
    have hrq : (z ^ (S.q ^ 2 + 1) * (S.h ^ a)⁻¹) ^ S.q = z ^ (S.q ^ 2 + 1) * (S.h ^ a)⁻¹ := by
      rcases h0 with h0 | h0
      · exact absurd h0 S.ω_ne_zero
      · exact (sub_eq_zero.mp h0).symm
    refine ⟨z ^ (S.q ^ 2 + 1) * (S.h ^ a)⁻¹, S.mem_F.mpr hrq, ?_, ?_⟩
    · exact mul_ne_zero (pow_ne_zero _ hz) (inv_ne_zero (S.h_pow_ne_zero a))
    · field_simp

/-- The trace condition `Tr(ν_a w) = 0` says `w ∈ h ^ a · F`. -/
theorem tr2_nu_eq_zero_iff (a : ℕ) (w : K) :
    S.tr2 (S.nu a * w) = 0 ↔ ∃ r ∈ S.F, w = S.h ^ a * r := by
  have hha : S.h ^ a ≠ 0 := S.h_pow_ne_zero a
  constructor
  · intro h0
    have hw : S.nu a * w = S.ω * (w * (S.h ^ a)⁻¹) := by
      unfold nu
      ring
    rw [hw, S.tr2_omega, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact absurd h0 S.ω_ne_zero
    · refine ⟨w * (S.h ^ a)⁻¹, S.mem_F.mpr (sub_eq_zero.mp h0).symm, ?_⟩
      field_simp
  · rintro ⟨r, hrF, rfl⟩
    have hw : S.nu a * (S.h ^ a * r) = S.ω * r := by
      unfold nu
      field_simp
    rw [hw, S.tr2_omega, S.mem_F.mp hrF, sub_self, mul_zero]

theorem pow_q_natCast (n : ℕ) : (n : K) ^ S.q = n :=
  map_natCast (iterateFrobenius K p S.e) n

theorem pow_q_four : (4 : K) ^ S.q = 4 := by
  have := S.pow_q_natCast 4
  exact_mod_cast this

theorem pow_q_pow_q_of_mem_L {ν : K} (hν : ν ∈ S.L) : (ν ^ S.q) ^ S.q = ν := by
  rw [← pow_mul, ← pow_two]
  exact S.mem_L.mp hν

theorem sub_pow_q2 (a b : K) : (a - b) ^ (S.q ^ 2) = a ^ (S.q ^ 2) - b ^ (S.q ^ 2) := by
  rw [sub_eq_add_neg, S.add_pow_q2, (S.q_odd.pow).neg_pow, ← sub_eq_add_neg]

theorem sub_pow_q1 (a b : K) : (a - b) ^ S.q = a ^ S.q - b ^ S.q := by
  rw [sub_eq_add_neg, S.add_pow_q1, S.neg_pow_q, ← sub_eq_add_neg]

/-- Frobenius of the discriminant expression. -/
theorem pow_q_mul_disc (u v : K) : (u * v) ^ S.q = u ^ S.q * v ^ S.q := mul_pow u v S.q

/-- `Tr(h ν^q X) = h ν^q X + h^q ν X^q` for `ν ∈ L`. -/
theorem tr2_hconj {ν : K} (hν : ν ∈ S.L) (X : K) :
    S.tr2 (S.h * ν ^ S.q * X) = S.h * ν ^ S.q * X + S.h ^ S.q * ν * X ^ S.q := by
  unfold tr2
  rw [mul_pow, mul_pow, S.pow_q_pow_q_of_mem_L hν]

/-- The discriminant with an arbitrary multiplier `l`. -/
def disL (l x y : K) : K :=
  (S.tr2 (l * (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y))) ^ 2
    - 4 * S.tr2 (l * x ^ (S.q ^ 2 + 1)) * S.tr2 (l * y ^ (S.q ^ 2 + 1))

theorem dis_eq_disL (a : ℕ) (x y : K) : S.dis a x y = S.disL (S.nu a) x y := rfl

theorem disL_smul {c : K} (hc : c ∈ S.F) (l x y : K) :
    S.disL (c * l) x y = c ^ 2 * S.disL l x y := by
  unfold disL
  rw [show c * l * (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y)
      = c * (l * (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y)) by ring,
    show c * l * x ^ (S.q ^ 2 + 1) = c * (l * x ^ (S.q ^ 2 + 1)) by ring,
    show c * l * y ^ (S.q ^ 2 + 1) = c * (l * y ^ (S.q ^ 2 + 1)) by ring,
    S.tr2_smul c hc, S.tr2_smul c hc, S.tr2_smul c hc]
  ring

/-- Algebra: the discriminant of `h ν^q` against `h^{q+1}` times that of `ν`, given
`h Δ = h^q Δ^q`. Pure polynomial identity in the atoms. -/
theorem disc_identity (H H' n n' B0 B1 A0 A1 C0 C1 : K)
    (hE : H * (B0 ^ 2 - 4 * A0 * C0) = H' * (B1 ^ 2 - 4 * A1 * C1)) :
    (H * n' * B0 + H' * n * B1) ^ 2
        - 4 * (H * n' * A0 + H' * n * A1) * (H * n' * C0 + H' * n * C1)
      = H * H' * ((n * B0 + n' * B1) ^ 2 - 4 * (n * A0 + n' * A1) * (n * C0 + n' * C1)) := by
  linear_combination (H * n' ^ 2 - H' * n ^ 2) * hE

/-- `h Δ` is a square of `w = d (x ȳ - x̄ y)`, which lies in `L`, and `h Δ = h^q Δ^q` when
the form vanishes on `(x, y)`. -/
theorem w_conj (x y : K) : (S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y)) ^ (S.q ^ 2)
    = S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) := by
  rw [mul_pow, S.d_pow_q_sq, S.sub_pow_q2, mul_pow, mul_pow, S.pow_q2_q2 y, S.pow_q2_q2 x]
  ring

theorem tr2_mul_expand (ν X : K) : S.tr2 (ν * X) = ν * X + ν ^ S.q * X ^ S.q := by
  unfold tr2
  rw [mul_pow]

/-- For a totally isotropic pair, `h Δ = h^q Δ^q` where `Δ = β² - 4 A C`. -/
theorem hE_of_ti {x y : K} (ht : S.B x y = 0) :
    S.h * ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
        - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1))
      = S.h ^ S.q * (((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ S.q) ^ 2
        - 4 * (x ^ (S.q ^ 2 + 1)) ^ S.q * (y ^ (S.q ^ 2 + 1)) ^ S.q) := by
  have hw := S.B_eq_tr2 x y
  rw [ht] at hw
  unfold tr2 at hw
  set w := S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) with hw_def
  have hwq : w ^ S.q = -w := by linear_combination -hw
  have hΔ : S.h * ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
        - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1)) = w ^ 2 := by
    rw [hw_def, ← S.d_sq, pow_succ x (S.q ^ 2), pow_succ y (S.q ^ 2)]
    ring
  have hD : ∀ u : K, (u ^ 2) ^ S.q = (u ^ S.q) ^ 2 := fun u => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hΔq : ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
        - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1)) ^ S.q
      = ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ S.q) ^ 2
        - 4 * (x ^ (S.q ^ 2 + 1)) ^ S.q * (y ^ (S.q ^ 2 + 1)) ^ S.q := by
    rw [S.sub_pow_q1, mul_pow, mul_pow, S.pow_q_four, hD]
  have hfix : (S.h * ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
        - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1))) ^ S.q
      = S.h * ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
        - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1)) := by
    rw [hΔ, show (w ^ 2) ^ S.q = (w ^ S.q) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm], hwq,
      neg_sq]
  rw [mul_pow, hΔq] at hfix
  exact hfix.symm

/-- `ν_{q-a} = c · h · ν_a^q` for some `c ∈ F^×`. -/
theorem nu_pair {a : ℕ} (ha : a ≤ S.q) :
    ∃ c ∈ S.F, c ≠ 0 ∧ S.nu (S.q - a) = c * (S.h * (S.nu a) ^ S.q) := by
  have hN0 : S.h ^ (S.q + 1) ≠ 0 := pow_ne_zero _ S.h_ne_zero
  have hhq : S.h ^ S.q = S.h ^ (S.q + 1) * S.h⁻¹ := by
    have := S.h_ne_zero
    rw [pow_succ]
    field_simp
  have hN : S.h ^ (S.q + 1) = S.h ^ a * S.h ^ (S.q - a) * S.h := by
    have h1 : S.h ^ a * S.h ^ (S.q - a) = S.h ^ S.q := by
      rw [← pow_add, Nat.add_sub_cancel' ha]
    calc S.h ^ (S.q + 1) = S.h ^ S.q * S.h := pow_succ _ _
      _ = (S.h ^ a * S.h ^ (S.q - a)) * S.h := by rw [h1]
  refine ⟨-((S.h ^ (S.q + 1)) ^ a * (S.h ^ (S.q + 1))⁻¹), ?_, ?_, ?_⟩
  · exact S.F.neg_mem (S.F.mul_mem (S.F.pow_mem S.N_mem_F a) (S.F.inv_mem S.N_mem_F))
  · exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hN0) (inv_ne_zero hN0))
  · have hXq : (S.h ^ a) ^ S.q = (S.h ^ (S.q + 1)) ^ a * (S.h ^ a)⁻¹ := by
      rw [← pow_mul, mul_comm, pow_mul, hhq, mul_pow, inv_pow]
    unfold nu
    rw [mul_pow, inv_pow, S.ω_pow_q, hXq]
    have hX : S.h ^ a ≠ 0 := S.h_pow_ne_zero a
    have hY : S.h ^ (S.q - a) ≠ 0 := pow_ne_zero _ S.h_ne_zero
    have hNa : (S.h ^ (S.q + 1)) ^ a ≠ 0 := pow_ne_zero _ hN0
    field_simp
    rw [hN]
    ring

theorem disL_hnu {ν x y : K} (hν : ν ∈ S.L) (ht : S.B x y = 0) :
    S.disL (S.h * ν ^ S.q) x y = S.h ^ (S.q + 1) * S.disL ν x y := by
  unfold disL
  rw [S.tr2_hconj hν, S.tr2_hconj hν, S.tr2_hconj hν, S.tr2_mul_expand, S.tr2_mul_expand,
    S.tr2_mul_expand]
  rw [show S.h ^ (S.q + 1) = S.h * S.h ^ S.q from pow_succ' _ _]
  have := disc_identity S.h (S.h ^ S.q) ν (ν ^ S.q)
    (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ S.q)
    (x ^ (S.q ^ 2 + 1)) ((x ^ (S.q ^ 2 + 1)) ^ S.q)
    (y ^ (S.q ^ 2 + 1)) ((y ^ (S.q ^ 2 + 1)) ^ S.q) (S.hE_of_ti ht)
  linear_combination this

theorem dis_pair {a : ℕ} (ha : a ≤ S.q) {x y : K} (ht : S.B x y = 0) :
    ∃ c ∈ S.F, c ≠ 0 ∧ S.dis (S.q - a) x y = c ^ 2 * (S.h ^ (S.q + 1) * S.dis a x y) := by
  obtain ⟨c, hcF, hc0, hν⟩ := S.nu_pair ha
  refine ⟨c, hcF, hc0, ?_⟩
  rw [S.dis_eq_disL, S.dis_eq_disL, hν, S.disL_smul hcF, S.disL_hnu (S.nu_mem_L a) ht]

theorem two_ne (S : Setting K p) : (2 : K) ≠ 0 := by
  intro h0
  have h1 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
  rw [CharP.cast_eq_zero_iff K p] at h1
  have hle := Nat.le_of_dvd (by norm_num) h1
  have hp2 := (Fact.out : p.Prime).two_le
  obtain ⟨k, hk⟩ := S.odd_p
  omega

/-- `h Δ = w²` with `w = d (x ȳ - x̄ y)` and `Δ = β² - 4AC` (no isotropy needed). -/
theorem h_mul_disc (x y : K) : S.h * ((x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2
    - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1))
    = (S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y)) ^ 2 := by
  rw [← S.d_sq, pow_succ x (S.q ^ 2), pow_succ y (S.q ^ 2)]
  ring

theorem w_mem_L (x y : K) : S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) ∈ S.L := by
  rw [mem_L]
  exact S.w_conj x y

theorem four_mem_F : (4 : K) ∈ S.F := by
  have h4 : (4 : K) = 1 + 1 + 1 + 1 := by norm_num
  rw [h4]
  exact S.F.add_mem (S.F.add_mem (S.F.add_mem S.F.one_mem S.F.one_mem) S.F.one_mem) S.F.one_mem

/-- In `L`, a nonzero element `t` satisfies `t ^ (q² - 1) = 1`. -/
theorem pow_q2_sub_one_of_mem_L {t : K} (ht : t ∈ S.L) (ht0 : t ≠ 0) :
    t ^ (S.q ^ 2 - 1) = 1 := by
  have h1 : t ^ S.q ^ 2 = t := S.mem_L.mp ht
  have hq : S.q ^ 2 = (S.q ^ 2 - 1) + 1 := by
    have : 1 ≤ S.q ^ 2 := Nat.one_le_pow _ _ (by have := S.q_ge_three; omega)
    omega
  have h2 : t ^ (S.q ^ 2 - 1) * t = 1 * t := by
    rw [← pow_succ, ← hq, h1, one_mul]
  exact mul_right_cancel₀ ht0 h2

/-- Part 1 of Proposition C: the coefficients of the form on a line are not all zero. -/
theorem coeff_not_all_zero {x y : K}
    (hind : ∀ s t : K, s ∈ S.F → t ∈ S.F → s * x + t * y = 0 → s = 0 ∧ t = 0) (a : ℕ) :
    ¬ (S.cA a x = 0 ∧ S.cB a x y = 0 ∧ S.cC a y = 0) := by
  rintro ⟨hA, hB, hC⟩
  obtain ⟨a1, ha1F, hA'⟩ := (S.tr2_nu_eq_zero_iff a _).mp hA
  obtain ⟨b1, hb1F, hB'⟩ := (S.tr2_nu_eq_zero_iff a _).mp hB
  obtain ⟨c1, hc1F, hC'⟩ := (S.tr2_nu_eq_zero_iff a _).mp hC
  have hD1 : b1 ^ 2 - 4 * a1 * c1 ∈ S.F := by
    refine S.F.sub_mem (S.F.pow_mem hb1F 2) (S.F.mul_mem (S.F.mul_mem ?_ ha1F) hc1F)
    exact S.four_mem_F
  have hΔ : (x * y ^ (S.q ^ 2) + x ^ (S.q ^ 2) * y) ^ 2 - 4 * x ^ (S.q ^ 2 + 1) * y ^ (S.q ^ 2 + 1)
      = (S.h ^ a) ^ 2 * (b1 ^ 2 - 4 * a1 * c1) := by
    rw [hA', hB', hC']
    ring
  by_cases hD : b1 ^ 2 - 4 * a1 * c1 = 0
  · by_cases ha0 : a1 = 0
    · have hb2 : b1 ^ 2 = 0 := by
        rw [ha0] at hD
        simpa using hD
      have hb0 : b1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp hb2
      have hx : x ^ (S.q ^ 2 + 1) = 0 := by rw [hA', ha0, mul_zero]
      have hx0 : x = 0 := (pow_eq_zero_iff (by omega)).mp hx
      obtain ⟨h1, -⟩ := hind 1 0 S.F.one_mem S.F.zero_mem (by simp [hx0])
      exact one_ne_zero h1
    · have hs : -b1 ∈ S.F := S.F.neg_mem hb1F
      have ht : a1 + a1 ∈ S.F := S.F.add_mem ha1F ha1F
      have hN : ((-b1) * x + (a1 + a1) * y) ^ (S.q ^ 2 + 1) = 0 := by
        rw [S.norm_expand hs ht, hA', hB', hC']
        linear_combination (-(S.h ^ a * a1)) * hD
      have hz0 : (-b1) * x + (a1 + a1) * y = 0 := (pow_eq_zero_iff (by omega)).mp hN
      obtain ⟨-, h2⟩ := hind (-b1) (a1 + a1) hs ht hz0
      have h3 : (2 : K) * a1 = 0 := by linear_combination h2
      rcases mul_eq_zero.mp h3 with h4 | h4
      · exact two_ne S h4
      · exact ha0 h4
  · obtain ⟨k, hk⟩ := S.exists_N_pow_of_mem_F hD1 hD
    have hDu : b1 ^ 2 - 4 * a1 * c1 = (S.ω ^ k) ^ 2 := by
      rw [hk, show (S.ω ^ k) ^ 2 = (S.ω ^ 2) ^ k by rw [← pow_mul, ← pow_mul, mul_comm],
        S.ω_sq]
    have hu0 : S.ω ^ k ≠ 0 := pow_ne_zero _ S.ω_ne_zero
    have hμ : S.h ^ a ≠ 0 := S.h_pow_ne_zero a
    have key : S.h * ((S.h ^ a) ^ 2 * (S.ω ^ k) ^ 2)
        = (S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y)) ^ 2 := by
      have := S.h_mul_disc x y
      rw [hΔ, hDu] at this
      exact this
    have ht'sq : (S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) * ((S.h ^ a) * S.ω ^ k)⁻¹) ^ 2
        = S.h := by
      field_simp
      linear_combination -key
    have ht'L : S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) * ((S.h ^ a) * S.ω ^ k)⁻¹ ∈ S.L :=
      S.L.mul_mem (S.w_mem_L x y)
        (S.L.inv_mem (S.L.mul_mem (S.L.pow_mem S.h_mem_L a) (S.L.pow_mem S.ω_mem_L k)))
    have ht'0 : S.d * (x * y ^ (S.q ^ 2) - x ^ (S.q ^ 2) * y) * ((S.h ^ a) * S.ω ^ k)⁻¹ ≠ 0 := by
      intro h0
      apply S.h_ne_zero
      rw [← ht'sq, h0]
      ring
    have hpow := S.pow_q2_sub_one_of_mem_L ht'L ht'0
    have h1 : S.h ^ ((S.q - 1) * ((S.q + 1) / 2)) = 1 := by
      rw [← ht'sq, ← pow_mul, S.half_mul, hpow]
    have hneg := S.h_pow_half
    have h2 : (2 : K) = 0 := by linear_combination hneg - h1
    exact two_ne S h2

theorem dis_mem_F (a : ℕ) (x y : K) : S.dis a x y ∈ S.F :=
  S.F.sub_mem (S.F.pow_mem (S.cB_mem_F a x y) 2)
    (S.F.mul_mem (S.F.mul_mem S.four_mem_F (S.cA_mem_F a x)) (S.cC_mem_F a y))

/-- Trace is linear over `F` for the quadratic expansion. -/
theorem tr2_quad {ν : K} {s t : K} (hs : s ∈ S.F) (ht : t ∈ S.F) (A β C : K) :
    S.tr2 (ν * (s ^ 2 * A + s * t * β + t ^ 2 * C))
      = s ^ 2 * S.tr2 (ν * A) + s * t * S.tr2 (ν * β) + t ^ 2 * S.tr2 (ν * C) := by
  have h2 : s ^ 2 ∈ S.F := S.F.pow_mem hs 2
  have h3 : s * t ∈ S.F := S.F.mul_mem hs ht
  have h4 : t ^ 2 ∈ S.F := S.F.pow_mem ht 2
  rw [mul_add, mul_add, S.tr2_add, S.tr2_add, show ν * (s ^ 2 * A) = s ^ 2 * (ν * A) by ring,
    show ν * (s * t * β) = s * t * (ν * β) by ring, show ν * (t ^ 2 * C) = t ^ 2 * (ν * C) by ring,
    S.tr2_smul _ h2, S.tr2_smul _ h3, S.tr2_smul _ h4]

theorem N_not_square_K {u : K} (hu : u ∈ S.F) : S.h ^ (S.q + 1) ≠ u * u := by
  intro hN
  obtain ⟨m, hm⟩ := S.q_odd
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact pow_ne_zero _ S.h_ne_zero (by rw [hN, mul_zero])
  have hu1 : u ^ (S.q - 1) = 1 := by
    have h1 : u ^ S.q = u := S.mem_F.mp hu
    rw [S.q_pow_eq] at h1
    apply mul_right_cancel₀ hu0
    rw [one_mul]
    exact h1
  have h1 : (S.h ^ (S.q + 1)) ^ m = 1 := by
    rw [hN, ← pow_two, ← pow_mul, show 2 * m = S.q - 1 by omega, hu1]
  have h2 : (S.h ^ (S.q + 1)) ^ m = S.h ^ ((S.q - 1) * ((S.q + 1) / 2)) := by
    rw [← pow_mul]
    congr 1
    rw [hm]
    have e1 : 2 * m + 1 - 1 = 2 * m := by omega
    have e2 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    rw [e1, e2]
    ring
  rw [h2, S.h_pow_half] at h1
  have h3 : (2 : K) = 0 := by linear_combination -h1
  exact two_ne S h3

noncomputable instance instFintypeF : Fintype S.F := Fintype.ofFinite _

noncomputable instance instDecEqF : DecidableEq S.F := Classical.decEq _

theorem ringChar_F : ringChar S.F ≠ 2 := by
  rw [ringChar.eq S.F p]
  intro h2
  obtain ⟨k, hk⟩ := S.odd_p
  omega

/-- Number of nonzero `(s, t) ∈ F²` whose point lies in class `a`: `(q - 1)(1 + χ(disc))`. -/
theorem card_class_F (a : ℕ) (ha : a < S.q + 1) {x y : K}
    (hind : ∀ s t : K, s ∈ S.F → t ∈ S.F → s * x + t * y = 0 → s = 0 ∧ t = 0) :
    ((Nat.card {st : S.F × S.F // st ≠ 0 ∧ S.InClass a ((st.1 : K) * x + (st.2 : K) * y)} : ℕ) : ℤ)
      = ((S.q : ℤ) - 1) * (1 + quadraticChar S.F ⟨S.dis a x y, S.dis_mem_F a x y⟩) := by
  have hcardF : Fintype.card S.F = S.q := by
    rw [← S.natCard_F, Nat.card_eq_fintype_card]
  set αF : S.F := ⟨S.cA a x, S.cA_mem_F a x⟩ with hαF
  set βF : S.F := ⟨S.cB a x y, S.cB_mem_F a x y⟩ with hβF
  set γF : S.F := ⟨S.cC a y, S.cC_mem_F a y⟩ with hγF
  have hnot : ¬ (αF = 0 ∧ βF = 0 ∧ γF = 0) := by
    rintro ⟨h1, h2, h3⟩
    apply S.coeff_not_all_zero hind a
    refine ⟨?_, ?_, ?_⟩
    · simpa [αF] using congrArg Subtype.val h1
    · simpa [βF] using congrArg Subtype.val h2
    · simpa [γF] using congrArg Subtype.val h3
  have hcard := card_zeros_form S.ringChar_F αF βF γF hnot
  rw [hcardF] at hcard
  have hdisc : βF ^ 2 - 4 * αF * γF = ⟨S.dis a x y, S.dis_mem_F a x y⟩ := by
    apply Subtype.ext
    have h4 : (((4 : S.F)) : K) = 4 := rfl
    simp only [αF, βF, γF, dis, Subfield.coe_sub, Subfield.coe_mul, SubmonoidClass.coe_pow, h4]
  rw [hdisc] at hcard
  have hz : ∀ st : S.F × S.F, st ≠ 0 → (st.1 : K) * x + (st.2 : K) * y ≠ 0 := by
    intro st hst h0
    obtain ⟨h1, h2⟩ := hind _ _ st.1.2 st.2.2 h0
    apply hst
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hiff : ∀ st : S.F × S.F, st ≠ 0 →
      (S.InClass a ((st.1 : K) * x + (st.2 : K) * y)
        ↔ αF * st.1 ^ 2 + βF * st.1 * st.2 + γF * st.2 ^ 2 = 0) := by
    intro st hst
    rw [S.inClass_iff_tr2 ha (hz st hst), S.norm_expand st.1.2 st.2.2, S.tr2_quad st.1.2 st.2.2]
    have hcoe : ((αF * st.1 ^ 2 + βF * st.1 * st.2 + γF * st.2 ^ 2 : S.F) : K)
        = S.cA a x * (st.1 : K) ^ 2 + S.cB a x y * (st.1 : K) * (st.2 : K)
          + S.cC a y * (st.2 : K) ^ 2 := by
      simp [αF, βF, γF]
    unfold cA cB cC at hcoe
    constructor
    · intro h0
      apply Subtype.ext
      rw [hcoe]
      simp only [ZeroMemClass.coe_zero]
      linear_combination h0
    · intro h0
      have h0' := congrArg Subtype.val h0
      rw [hcoe] at h0'
      simp only [ZeroMemClass.coe_zero] at h0'
      linear_combination h0'
  have hset : Nat.card {st : S.F × S.F // st ≠ 0 ∧ S.InClass a ((st.1 : K) * x + (st.2 : K) * y)}
      = (Finset.univ.filter (fun st : S.F × S.F =>
          st ≠ 0 ∧ αF * st.1 ^ 2 + βF * st.1 * st.2 + γF * st.2 ^ 2 = 0)).card := by
    classical
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro st _
    constructor
    · rintro ⟨hst, hin⟩
      exact ⟨hst, (hiff st hst).mp hin⟩
    · rintro ⟨hst, hpoly⟩
      exact ⟨hst, (hiff st hst).mpr hpoly⟩
  rw [hset]
  exact_mod_cast hcard

theorem chi_N : quadraticChar S.F ⟨S.h ^ (S.q + 1), S.N_mem_F⟩ = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare]
  rintro ⟨r, hr⟩
  apply S.N_not_square_K r.2
  have := congrArg Subtype.val hr
  simpa using this

/-- The character flips sign under the pairing `a ↔ q - a`. -/
theorem chi_pair {a : ℕ} (ha : a ≤ S.q) {x y : K} (ht : S.B x y = 0) :
    quadraticChar S.F ⟨S.dis (S.q - a) x y, S.dis_mem_F (S.q - a) x y⟩
      = -quadraticChar S.F ⟨S.dis a x y, S.dis_mem_F a x y⟩ := by
  obtain ⟨c, hcF, hc0, hd⟩ := S.dis_pair ha ht
  have hcne : (⟨c, hcF⟩ : S.F) ≠ 0 := fun h => hc0 (congrArg Subtype.val h)
  have e : (⟨S.dis (S.q - a) x y, S.dis_mem_F (S.q - a) x y⟩ : S.F)
      = ⟨c, hcF⟩ ^ 2 * (⟨S.h ^ (S.q + 1), S.N_mem_F⟩ * ⟨S.dis a x y, S.dis_mem_F a x y⟩) := by
    apply Subtype.ext
    simp only [Subfield.coe_mul, SubmonoidClass.coe_pow]
    exact hd
  rw [e, map_mul, map_mul, quadraticChar_sq_one' hcne, S.chi_N]
  ring

/-- The number of nonzero `(s, t)` with the point in class `a` or `q - a`, for a totally
isotropic line. -/
theorem card_union_class {a : ℕ} (ha : a ≤ S.q) {x y : K}
    (hind : ∀ s t : K, s ∈ S.F → t ∈ S.F → s * x + t * y = 0 → s = 0 ∧ t = 0)
    (ht : S.B x y = 0) :
    ((Nat.card {st : S.F × S.F // st ≠ 0 ∧
        (S.InClass a ((st.1 : K) * x + (st.2 : K) * y)
          ∨ S.InClass (S.q - a) ((st.1 : K) * x + (st.2 : K) * y))} : ℕ) : ℤ)
      = 2 * ((S.q : ℤ) - 1) := by
  classical
  obtain ⟨m, hm⟩ := S.q_odd
  have ha_lt : a < S.q + 1 := by omega
  have hb_lt : S.q - a < S.q + 1 := by omega
  have hsplit : (Finset.univ.filter (fun st : S.F × S.F =>
      st ≠ 0 ∧ (S.InClass a ((st.1 : K) * x + (st.2 : K) * y)
        ∨ S.InClass (S.q - a) ((st.1 : K) * x + (st.2 : K) * y))))
      = Finset.univ.filter (fun st : S.F × S.F =>
          st ≠ 0 ∧ S.InClass a ((st.1 : K) * x + (st.2 : K) * y))
        ∪ Finset.univ.filter (fun st : S.F × S.F =>
          st ≠ 0 ∧ S.InClass (S.q - a) ((st.1 : K) * x + (st.2 : K) * y)) := by
    ext st
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  have hdisj : Disjoint (Finset.univ.filter (fun st : S.F × S.F =>
          st ≠ 0 ∧ S.InClass a ((st.1 : K) * x + (st.2 : K) * y)))
        (Finset.univ.filter (fun st : S.F × S.F =>
          st ≠ 0 ∧ S.InClass (S.q - a) ((st.1 : K) * x + (st.2 : K) * y))) := by
    rw [Finset.disjoint_filter]
    rintro st - ⟨-, h1⟩ ⟨-, h2⟩
    have := S.inClass_unique h1 h2
    omega
  have hcard : ∀ P : S.F × S.F → Prop, [DecidablePred P] →
      Nat.card {st : S.F × S.F // P st} = (Finset.univ.filter P).card := by
    intro P _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hA := S.card_class_F a ha_lt hind
  have hB := S.card_class_F (S.q - a) hb_lt hind
  rw [hcard] at hA hB
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, hsplit, Finset.card_union_of_disjoint hdisj]
  push_cast
  rw [hA, hB, S.chi_pair ha ht]
  ring

end Setting

end BipartiteDD.SingerC
