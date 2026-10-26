import BipartiteDD.LeanAll.Core.HaarCore
import BipartiteDD.LeanAll.Swar
import Mathlib.Data.ZMod.Basic

/-! # Batch checks of words in `SL(2, p) × Z_n`, by packed arithmetic (over `Core/HaarCore.lean`)

A copy of `HaarSwar.lean` whose definitions of the computation are in `Core/HaarCore.lean` (no Mathlib).

A *batch* is `N` slots. Slot `j` carries a word of `L` letters, given by `L` digits (4 bits each) packed in one
field of the certificate number `Dig`. Letter `t` with digit `u` is the matrix `(e, f; g, h)` and the shift `zw` of
`lt t u` (step `t` may use the inverses). Starting from the identity, the kernel multiplies all `N` slot states by
their letters at once, `w`-bit fields, reducing mod `p` (an approximate Barrett step, then one conditional
subtraction, then a check that every field is below `p`) and mod `n`.

`batch_sound`: if `batchOK` holds, then for every slot the product of its letters has the claimed final entries
(in `ZMod p` and `ZMod n`). -/

namespace BipartiteDD.LeanAll.HaarSwar2

open BipartiteDD.LeanAll.Swar


/-! ## Fieldwise facts -/

section Facts

variable {P : Prm}

theorem shr_land_one_lt32 (x : ℕ) (hx : x < 32) : (x >>> 4) &&& 1 = if 16 ≤ x then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  split_ifs with h <;> omega

theorem shr_land_one_half (w x : ℕ) (hw : 1 ≤ w) (hx : x < 2 ^ w) :
    (x >>> (w - 1)) &&& 1 = if 2 ^ (w - 1) ≤ x then 1 else 0 := by
  rw [Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod]
  have e : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hp : 0 < 2 ^ (w - 1) := Nat.two_pow_pos _
  split_ifs with h
  · have h1 : x / 2 ^ (w - 1) = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    omega
  · have h1 : x / 2 ^ (w - 1) = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem land_full (w x : ℕ) (hx : x < 2 ^ w) (b : ℕ) (hb : b ≤ 1) :
    x &&& (b * (2 ^ w - 1)) = if b = 1 then x else 0 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with rfl | rfl
  · simp
  · simp only [one_mul, if_true]
    rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]

theorem land_half_eq_zero (w x : ℕ) (hw : 1 ≤ w) (hx : x < 2 ^ w) (h : x &&& 2 ^ (w - 1) = 0) :
    x < 2 ^ (w - 1) := by
  by_contra hc
  push_neg at hc
  have hb : x.testBit (w - 1) = true := by
    rw [Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq]
    have e : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have h1 : x / 2 ^ (w - 1) = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    omega
  have : (x &&& 2 ^ (w - 1)).testBit (w - 1) = true := by
    rw [Nat.testBit_and, hb, Nat.testBit_two_pow_self]; rfl
  rw [h] at this
  simp at this

end Facts

/-! ## The packed steps, fieldwise -/

section Fieldwise

variable {w N : ℕ}

/-- The packing of `f` with `w`-bit fields and `N` slots. -/
local notation "pk" f => pkF w f N

theorem lt_two_pow_of_le_half {w x : ℕ} (hw : 1 ≤ w) (h : x < 2 ^ (w - 1)) : x < 2 ^ w :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem thr_eq (hw : 8 ≤ w) {ONES Dt : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {dt : ℕ → ℕ}
    (hD : Dt = pkF w dt N) (hdt : ∀ j < N, dt j < 16) {u : ℕ} (hu : u ≤ 16) :
    thr ONES Dt u = pkF w (fun j => if u ≤ dt j then 1 else 0) N := by
  have h32 : (32 : ℕ) ≤ 2 ^ w := by
    calc (32 : ℕ) = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : Dt + (16 - u) * ONES = pkF w (fun j => dt j + (16 - u)) N := by
    rw [hD, hO, ← pkF_mul, pkF_add]; simp
  have h1 : (1 : ℕ) < 2 ^ (w - 4) := Nat.one_lt_two_pow (by omega)
  unfold thr
  rw [e1, hO, pkF_shr_land (by omega) (by omega) h1 (fun j hj => by have := hdt j hj; omega)]
  apply pkF_congr
  intro j hj
  rw [shr_land_one_lt32 _ (by have := hdt j hj; omega)]
  have := hdt j hj
  split_ifs <;> omega

theorem eqm_eq (hw : 8 ≤ w) {ONES Dt : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {dt : ℕ → ℕ}
    (hD : Dt = pkF w dt N) (hdt : ∀ j < N, dt j < 16) {u : ℕ} (hu : u < 16) :
    eqm ONES Dt u = pkF w (fun j => if dt j = u then 1 else 0) N := by
  unfold eqm
  rw [thr_eq hw hO hD hdt (by omega), thr_eq hw hO hD hdt (by omega), ← pkF_sub]
  · apply pkF_congr
    intro j _
    split_ifs <;> omega
  · intro j _
    split_ifs <;> omega

theorem selSum_eq (P : Prm) (hw : 8 ≤ P.w) {ONES Dt : ℕ} (hO : ONES = pkF P.w (fun _ => 1) N)
    {dt : ℕ → ℕ} (hD : Dt = pkF P.w dt N) (hdt : ∀ j < N, dt j < 16) {V : ℕ → ℕ} {v : ℕ → ℕ → ℕ}
    (hV : ∀ u, V u = pkF P.w (v u) N) {K : ℕ} (hK : K ≤ 16) (hv : ∀ u < K, ∀ j < N, v u j < 2 ^ P.w) :
    ∀ k ≤ K, selSum P ONES Dt V k = pkF P.w (fun j => if dt j < k then v (dt j) j else 0) N := by
  intro k
  induction k with
  | zero =>
    intro _
    show 0 = _
    rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp), pkF_const]
    simp
  | succ k ih =>
    intro hk
    show selSum P ONES Dt V k + (V k &&& (eqm ONES Dt k * (2 ^ P.w - 1))) = _
    rw [ih (by omega), eqm_eq hw hO hD hdt (by omega), mul_comm, ← pkF_mul, hV k,
      pkF_land (by omega) (hv k (by omega)), ← pkF_add]
    · apply pkF_congr
      intro j hj
      have hvk := hv k (by omega) j hj
      rw [show (2 ^ P.w - 1) * (if dt j = k then 1 else 0) = (if dt j = k then 1 else 0) * (2 ^ P.w - 1) by ring,
        land_full _ _ hvk _ (by split_ifs <;> omega)]
      by_cases h1 : dt j < k
      · have : dt j ≠ k := by omega
        simp [h1, this, show dt j < k + 1 by omega]
      · by_cases h2 : dt j = k
        · simp [h1, h2]
        · simp [h1, h2, show ¬ dt j < k + 1 by omega]
    · intro j _
      have : 1 ≤ 2 ^ P.w := Nat.one_le_two_pow
      split_ifs <;> simp <;> omega

theorem two_pow_split {w : ℕ} (hw : 1 ≤ w) : 2 ^ w = 2 ^ (w - 1) + 2 ^ (w - 1) := by
  have : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  omega

/-- The conditional subtraction: fields `< 2 ^ (w-1)`, subtract `q` where the field is `≥ q`. -/
theorem condsub_eq {w : ℕ} (hw : 1 ≤ w) {ONES V : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF w v N) (hb : ∀ j < N, v j < 2 ^ (w - 1)) {q : ℕ} (hq : q ≤ 2 ^ (w - 1)) :
    V - q * (((V + (2 ^ (w - 1) - q) * ONES) >>> (w - 1)) &&& ONES) =
      pkF w (fun j => v j - q * (if q ≤ v j then 1 else 0)) N := by
  have hs := two_pow_split hw
  have e1 : V + (2 ^ (w - 1) - q) * ONES = pkF w (fun j => v j + (2 ^ (w - 1) - q)) N := by
    rw [hV, hO, ← pkF_mul, pkF_add]; simp
  have h2 : (1 : ℕ) < 2 ^ (w - (w - 1)) := by
    rw [show w - (w - 1) = 1 by omega]; norm_num
  rw [e1, hO, pkF_shr_land (by omega) (by omega) h2 (fun j hj => by have := hb j hj; omega), ← pkF_mul,
    hV, ← pkF_sub]
  · apply pkF_congr
    intro j hj
    rw [shr_land_one_half w _ hw (by have := hb j hj; omega)]
    have := hb j hj
    split_ifs <;> omega
  · intro j hj
    rw [shr_land_one_half w _ hw (by have := hb j hj; omega)]
    have := hb j hj
    split_ifs <;> omega

theorem red_eq (P : Prm) (hv : P.valid) {ONES V : ℕ} (hO : ONES = pkF P.w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF P.w v N) (hb : ∀ j < N, v j < 2 * P.p * P.p) :
    ∃ r : ℕ → ℕ, red P ONES P.p V = pkF P.w r N ∧ ∀ j < N, r j ≤ v j ∧ r j ≡ v j [MOD P.p] := by
  obtain ⟨hw8, -, -, hp2, -, hsw, hpp, -, hbar, hmp⟩ := hv
  have hw : 1 ≤ P.w := by omega
  have hs := two_pow_split hw
  -- the quotient estimate
  have e1 : V * P.m = pkF P.w (fun j => P.m * v j) N := by rw [hV, pkF_mul, mul_comm]
  have hmv : ∀ j < N, P.m * v j < 2 ^ P.w := by
    intro j hj
    have := hb j hj
    calc P.m * v j ≤ P.m * (2 * P.p * P.p) := Nat.mul_le_mul_left _ this.le
      _ = 2 * P.p * P.p * P.m := by ring
      _ < 2 ^ P.w := hbar
  have hc : 2 ^ (P.w - P.s) - 1 < 2 ^ (P.w - P.s) := by
    have := Nat.one_le_two_pow (n := P.w - P.s); omega
  have eQ : ((V * P.m) >>> P.s) &&& ((2 ^ (P.w - P.s) - 1) * ONES) =
      pkF P.w (fun j => ((P.m * v j) >>> P.s) &&& (2 ^ (P.w - P.s) - 1)) N := by
    rw [e1, hO, ← pkF_const, pkF_shr_land (by omega) hsw hc hmv]
  set q : ℕ → ℕ := fun j => ((P.m * v j) >>> P.s) &&& (2 ^ (P.w - P.s) - 1) with hqdef
  have hq : ∀ j < N, P.p * q j ≤ v j := by
    intro j _
    have h1 : q j ≤ P.m * v j / 2 ^ P.s := by
      rw [hqdef, ← Nat.shiftRight_eq_div_pow]; exact Nat.and_le_left
    calc P.p * q j ≤ P.p * (P.m * v j / 2 ^ P.s) := Nat.mul_le_mul_left _ h1
      _ ≤ P.p * (P.m * v j) / 2 ^ P.s := Nat.mul_div_le_mul_div_assoc _ _ _
      _ ≤ v j := by
          apply Nat.div_le_of_le_mul
          calc P.p * (P.m * v j) = (P.m * P.p) * v j := by ring
            _ ≤ 2 ^ P.s * v j := Nat.mul_le_mul_right _ hmp
  have eR : V - P.p * pkF P.w q N = pkF P.w (fun j => v j - P.p * q j) N := by
    rw [← pkF_mul, hV, pkF_sub hq]
  have hr1 : ∀ j < N, v j - P.p * q j < 2 ^ (P.w - 1) := by
    intro j hj
    have := hb j hj
    omega
  have hpH : P.p ≤ 2 ^ (P.w - 1) := by nlinarith
  refine ⟨fun j => (v j - P.p * q j) - P.p * (if P.p ≤ v j - P.p * q j then 1 else 0), ?_, ?_⟩
  · simp only [red]
    rw [eQ, eR]
    exact condsub_eq hw hO rfl hr1 hpH
  · intro j hj
    have hqj := hq j hj
    dsimp only
    by_cases hc : P.p ≤ v j - P.p * q j
    · simp only [hc, if_true, mul_one]
      refine ⟨by omega, ?_⟩
      have e2 : v j = (v j - P.p * q j - P.p) + P.p * (q j + 1) := by rw [mul_add, mul_one]; omega
      show (v j - P.p * q j - P.p) % P.p = v j % P.p
      rw [e2, Nat.add_mul_mod_self_left, ← e2]
    · simp only [hc, if_false, mul_zero, Nat.sub_zero]
      refine ⟨by omega, ?_⟩
      have e2 : v j = (v j - P.p * q j) + P.p * q j := by omega
      show (v j - P.p * q j) % P.p = v j % P.p
      rw [e2, Nat.add_mul_mod_self_left, ← e2]

theorem redZ_eq (P : Prm) (hv : P.valid) {ONES V : ℕ} (hO : ONES = pkF P.w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF P.w v N) (hb : ∀ j < N, v j < 2 * P.n) :
    ∃ r : ℕ → ℕ, redZ P ONES V = pkF P.w r N ∧ ∀ j < N, r j ≤ v j ∧ r j ≡ v j [MOD P.n] := by
  obtain ⟨hw8, -, -, -, hn2, -, -, hnn, -, -⟩ := hv
  have hw : 1 ≤ P.w := by omega
  have hb' : ∀ j < N, v j < 2 ^ (P.w - 1) := fun j hj => by have := hb j hj; omega
  refine ⟨fun j => v j - P.n * (if P.n ≤ v j then 1 else 0), ?_, ?_⟩
  · simp only [redZ]
    exact condsub_eq hw hO hV hb' (by omega)
  · intro j _
    dsimp only
    by_cases hc : P.n ≤ v j
    · simp only [hc, if_true, mul_one]
      refine ⟨by omega, ?_⟩
      have e2 : v j = (v j - P.n) + P.n * 1 := by omega
      show (v j - P.n) % P.n = v j % P.n
      rw [e2, Nat.add_mul_mod_self_left, ← e2]
    · simp only [hc, if_false, mul_zero, Nat.sub_zero]
      exact ⟨le_refl _, rfl⟩

theorem below_spec {w : ℕ} (P : Prm) (hPw : P.w = w) (hw : 1 ≤ w) {ONES : ℕ}
    (hO : ONES = pkF w (fun _ => 1) N) {r : ℕ → ℕ} {q : ℕ} (hq : q ≤ 2 ^ (w - 1))
    (hr : ∀ j < N, r j < 2 ^ (w - 1)) (h : below P ONES q (pkF w r N) = true) : ∀ j < N, r j < q := by
  subst hPw
  have hs := two_pow_split hw
  unfold below at h
  rw [Nat.beq_eq] at h
  have e1 : pkF P.w r N + (2 ^ (P.w - 1) - q) * ONES = pkF P.w (fun j => r j + (2 ^ (P.w - 1) - q)) N := by
    rw [hO, ← pkF_mul, pkF_add]; simp
  have hH : 2 ^ (P.w - 1) < 2 ^ P.w := by have := Nat.two_pow_pos (P.w - 1); omega
  have hw0 : 0 < P.w := by omega
  rw [e1, hO, ← pkF_const, pkF_land (w := P.w) (B := N) hw0 (fun j hj => by have := hr j hj; omega)
    (fun _ _ => hH)] at h
  have h0 : pkF P.w (fun j => (r j + (2 ^ (P.w - 1) - q)) &&& 2 ^ (P.w - 1)) N = pkF P.w (fun _ => 0) N := by
    rw [h, pkF_const]; simp
  have := pkF_inj hw0 (fun j _ => Nat.and_lt_two_pow _ hH) (fun _ _ => by positivity) h0
  intro j hj
  have h1 := land_half_eq_zero P.w _ hw (by have := hr j hj; omega) (this j hj)
  omega

theorem dig_eq {w : ℕ} (hw : 0 < w) {ONES Dig : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {F : ℕ → ℕ}
    (hDig : Dig = pkF w F N) (hF : ∀ j < N, F j < 2 ^ w) {t : ℕ} (ht : 4 * t + 4 ≤ w) :
    (Dig >>> (4 * t)) &&& (15 * ONES) = pkF w (fun j => (F j >>> (4 * t)) &&& 15) N := by
  have hc : (15 : ℕ) < 2 ^ (w - 4 * t) := by
    calc (15 : ℕ) < 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (w - 4 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hDig, hO, ← pkF_const, pkF_shr_land hw (by omega) hc hF]

end Fieldwise

/-! ## One step, all steps -/

/-- One letter on a slot state, in `ℕ` (no reduction). -/
def mulSt (x : St) (l : Let) : St :=
  ⟨x.a * l.e + x.b * l.g, x.a * l.f + x.b * l.h, x.c * l.e + x.d * l.g, x.c * l.f + x.d * l.h, x.z + l.zw⟩

/-- Componentwise congruence: entries mod `p`, the `Z_n` part mod `n`. -/
def MEq (p n : ℕ) (x y : St) : Prop :=
  x.a ≡ y.a [MOD p] ∧ x.b ≡ y.b [MOD p] ∧ x.c ≡ y.c [MOD p] ∧ x.d ≡ y.d [MOD p] ∧ x.z ≡ y.z [MOD n]

theorem MEq.trans {p n : ℕ} {x y z : St} (h1 : MEq p n x y) (h2 : MEq p n y z) : MEq p n x z :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.1.trans h2.2.2.1, h1.2.2.2.1.trans h2.2.2.2.1,
    h1.2.2.2.2.trans h2.2.2.2.2⟩

theorem MEq.mulSt {p n : ℕ} {x y : St} (h : MEq p n x y) (l : Let) : MEq p n (mulSt x l) (mulSt y l) := by
  obtain ⟨ha, hb, hc, hd, hz⟩ := h
  exact ⟨(ha.mul_right _).add (hb.mul_right _), (ha.mul_right _).add (hb.mul_right _),
    (hc.mul_right _).add (hd.mul_right _), (hc.mul_right _).add (hd.mul_right _), hz.add_right _⟩

/-- `X` packs the slot states `xs`, all reduced. -/
def Rep (P : Prm) (X : St) (xs : ℕ → St) : Prop :=
  X.a = pkF P.w (fun j => (xs j).a) P.N ∧ X.b = pkF P.w (fun j => (xs j).b) P.N ∧
  X.c = pkF P.w (fun j => (xs j).c) P.N ∧ X.d = pkF P.w (fun j => (xs j).d) P.N ∧
  X.z = pkF P.w (fun j => (xs j).z) P.N ∧
  ∀ j < P.N, (xs j).a < P.p ∧ (xs j).b < P.p ∧ (xs j).c < P.p ∧ (xs j).d < P.p ∧ (xs j).z < P.n

/-- Letters below the moduli. -/
def LetOK (P : Prm) (lt : ℕ → ℕ → Let) : Prop :=
  ∀ t < P.L, ∀ u < P.Δ, (lt t u).e < P.p ∧ (lt t u).f < P.p ∧ (lt t u).g < P.p ∧ (lt t u).h < P.p ∧
    (lt t u).zw < P.n

/-- Digit `t` of a certificate field. -/
def digit (F t : ℕ) : ℕ := (F >>> (4 * t)) &&& 15

theorem digit_lt (F t : ℕ) : digit F t < 16 := Nat.and_lt_two_pow _ (by norm_num : (15 : ℕ) < 2 ^ 4)

theorem lin_eq {w N : ℕ} {X Y : ℕ} {x y : ℕ → ℕ} (hX : X = pkF w x N) (hY : Y = pkF w y N) (e g : ℕ) :
    X * e + Y * g = pkF w (fun j => x j * e + y j * g) N := by
  rw [hX, hY, mul_comm _ e, mul_comm _ g, ← pkF_mul, ← pkF_mul, ← pkF_add]
  exact pkF_congr (fun j _ => by ring)

theorem lin_bound {p a b e g : ℕ} (ha : a < p) (hb : b < p) (he : e < p) (hg : g < p) :
    a * e + b * g < 2 * p * p := by nlinarith

theorem step_sound (P : Prm) (hv : P.valid) {ONES : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) {Dig : ℕ} {F : ℕ → ℕ} (hDig : Dig = pkF P.w F P.N)
    (hF : ∀ j < P.N, F j < 2 ^ P.w) {t : ℕ} (ht : t < P.L) {X : St} {xs : ℕ → St} (hX : Rep P X xs)
    (hok : (stepP P ONES lt Dig t X).2 = true) :
    ∃ ys, Rep P (stepP P ONES lt Dig t X).1 ys ∧
      ∀ j < P.N, digit (F j) t < P.Δ ∧ MEq P.p P.n (ys j) (mulSt (xs j) (lt t (digit (F j) t))) := by
  have hv' := hv
  obtain ⟨hw8, hwL, hΔ, hp2, hn2, hsw, hpp, hnn, hbar, hmp⟩ := hv'
  obtain ⟨hXa, hXb, hXc, hXd, hXz, hxb⟩ := hX
  have hw : 0 < P.w := by omega
  have hw1 : 1 ≤ P.w := by omega
  have hs := two_pow_split hw1
  have hD := dig_eq hw hO hDig hF (t := t) (by omega)
  have hdt : ∀ j < P.N, (fun j => (F j >>> (4 * t)) &&& 15) j < 16 := fun j _ => digit_lt (F j) t
  simp only [stepP, Bool.and_eq_true, Nat.beq_eq] at hok
  obtain ⟨⟨⟨⟨⟨h0, hA⟩, hB⟩, hC⟩, hDd⟩, hZ⟩ := hok
  -- all digits are below Δ
  have hdΔ : ∀ j < P.N, digit (F j) t < P.Δ := by
    rw [thr_eq hw8 hO hD hdt hΔ] at h0
    have h0' : pkF P.w (fun j => if P.Δ ≤ (F j >>> (4 * t)) &&& 15 then 1 else 0) P.N =
        pkF P.w (fun _ => 0) P.N := by rw [h0, pkF_const]; simp
    have := pkF_inj hw (fun j _ => by split_ifs <;> simp [Nat.one_lt_two_pow_iff] <;> omega)
      (fun _ _ => by positivity) h0'
    intro j hj
    have h1 := this j hj
    unfold digit
    split_ifs at h1 with h2
    all_goals first | omega | simp at h1
  have hpH : P.p ≤ 2 ^ (P.w - 1) := by nlinarith
  have hpw : 2 * P.p * P.p ≤ 2 ^ P.w := by omega
  -- one entry: selection then reduction
  have entry : ∀ (Xu Xv : ℕ) (xu xv : ℕ → ℕ), Xu = pkF P.w xu P.N → Xv = pkF P.w xv P.N →
      (∀ j < P.N, xu j < P.p) → (∀ j < P.N, xv j < P.p) → (E G : ℕ → ℕ) →
      (∀ u < P.Δ, E u < P.p) → (∀ u < P.Δ, G u < P.p) →
      below P ONES P.p (red P ONES P.p (selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES))
        (fun u => Xu * E u + Xv * G u) P.Δ)) = true →
      ∃ r : ℕ → ℕ, red P ONES P.p (selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES))
        (fun u => Xu * E u + Xv * G u) P.Δ) = pkF P.w r P.N ∧
        ∀ j < P.N, r j < P.p ∧ r j ≡ xu j * E (digit (F j) t) + xv j * G (digit (F j) t) [MOD P.p] := by
    intro Xu Xv xu xv hu hvv hxu hxv E G hE hG hbelow
    have hsel := selSum_eq P hw8 hO hD hdt (fun u => lin_eq hu hvv (E u) (G u)) hΔ
      (fun u hu' j hj => lt_of_lt_of_le (lin_bound (hxu j hj) (hxv j hj) (hE u hu') (hG u hu')) hpw)
      P.Δ (le_refl _)
    have hsel' : selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * E u + Xv * G u) P.Δ =
        pkF P.w (fun j => xu j * E (digit (F j) t) + xv j * G (digit (F j) t)) P.N := by
      rw [hsel]
      exact pkF_congr (fun j hj => by simp only [digit] at hdΔ ⊢; simp [hdΔ j hj])
    obtain ⟨r, hr1, hr2⟩ := red_eq P hv hO hsel' (fun j hj =>
      lin_bound (hxu j hj) (hxv j hj) (hE _ (hdΔ j hj)) (hG _ (hdΔ j hj)))
    refine ⟨r, hr1, fun j hj => ⟨?_, (hr2 j hj).2⟩⟩
    rw [hr1] at hbelow
    have hrb : ∀ j < P.N, r j < 2 ^ (P.w - 1) := fun j hj =>
      lt_of_le_of_lt (hr2 j hj).1 (lt_of_lt_of_le (lin_bound (hxu j hj) (hxv j hj)
        (hE _ (hdΔ j hj)) (hG _ (hdΔ j hj))) hpp)
    exact below_spec P rfl hw1 hO hpH hrb hbelow j hj
  have hle : ∀ u < P.Δ, _ := fun u hu => hlt t ht u hu
  obtain ⟨ra, hra, hra'⟩ := entry X.a X.b _ _ hXa hXb (fun j hj => (hxb j hj).1) (fun j hj => (hxb j hj).2.1)
    (fun u => (lt t u).e) (fun u => (lt t u).g) (fun u hu => (hle u hu).1) (fun u hu => (hle u hu).2.2.1) hA
  obtain ⟨rb, hrb, hrb'⟩ := entry X.a X.b _ _ hXa hXb (fun j hj => (hxb j hj).1) (fun j hj => (hxb j hj).2.1)
    (fun u => (lt t u).f) (fun u => (lt t u).h) (fun u hu => (hle u hu).2.1) (fun u hu => (hle u hu).2.2.2.1) hB
  obtain ⟨rc, hrc, hrc'⟩ := entry X.c X.d _ _ hXc hXd (fun j hj => (hxb j hj).2.2.1)
    (fun j hj => (hxb j hj).2.2.2.1)
    (fun u => (lt t u).e) (fun u => (lt t u).g) (fun u hu => (hle u hu).1) (fun u hu => (hle u hu).2.2.1) hC
  obtain ⟨rd, hrd, hrd'⟩ := entry X.c X.d _ _ hXc hXd (fun j hj => (hxb j hj).2.2.1)
    (fun j hj => (hxb j hj).2.2.2.1)
    (fun u => (lt t u).f) (fun u => (lt t u).h) (fun u hu => (hle u hu).2.1) (fun u hu => (hle u hu).2.2.2.1) hDd
  -- the `Z_n` part
  have hzsel := selSum_eq P hw8 hO hD hdt (V := fun u => (lt t u).zw * ONES) (v := fun u _ => (lt t u).zw)
    (fun u => by show (lt t u).zw * ONES = pkF P.w (fun _ => (lt t u).zw) P.N; rw [pkF_const, hO]) hΔ
    (fun u hu j _ => lt_of_lt_of_le (hle u hu).2.2.2.2 (by
      have : P.n ≤ 2 ^ (P.w - 1) := by omega
      omega)) P.Δ (le_refl _)
  have hzv : X.z + selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => (lt t u).zw * ONES) P.Δ =
      pkF P.w (fun j => (xs j).z + (lt t (digit (F j) t)).zw) P.N := by
    rw [hzsel, hXz, ← pkF_add]
    exact pkF_congr (fun j hj => by simp only [digit] at hdΔ ⊢; simp [hdΔ j hj])
  obtain ⟨rz, hrz, hrz'⟩ := redZ_eq P hv hO hzv (fun j hj => by
    have := (hxb j hj).2.2.2.2; have := (hle _ (hdΔ j hj)).2.2.2.2; omega)
  have hrzb : ∀ j < P.N, rz j < P.n := by
    have hb' : ∀ j < P.N, rz j < 2 ^ (P.w - 1) := fun j hj => by
      have := (hrz' j hj).1; have := (hxb j hj).2.2.2.2; have := (hle _ (hdΔ j hj)).2.2.2.2; omega
    rw [hrz] at hZ
    exact below_spec P rfl hw1 hO (by omega) hb' hZ
  refine ⟨fun j => ⟨ra j, rb j, rc j, rd j, rz j⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact hra
  · exact hrb
  · exact hrc
  · exact hrd
  · exact hrz
  · intro j hj
    exact ⟨(hra' j hj).1, (hrb' j hj).1, (hrc' j hj).1, (hrd' j hj).1, hrzb j hj⟩
  · intro j hj
    exact ⟨hdΔ j hj, (hra' j hj).2, (hrb' j hj).2, (hrc' j hj).2, (hrd' j hj).2, (hrz' j hj).2⟩

/-- The first `t` steps. -/
def runT (P : Prm) (ONES : ℕ) (lt : ℕ → ℕ → Let) (Dig t : ℕ) : St × Bool :=
  Nat.rec (motive := fun _ => St × Bool) (⟨ONES, 0, 0, ONES, 0⟩, true)
    (fun t acc => let r := stepP P ONES lt Dig t acc.1; (r.1, acc.2 && r.2)) t

theorem runP_eq (P : Prm) (ONES : ℕ) (lt : ℕ → ℕ → Let) (Dig : ℕ) :
    runP P ONES lt Dig = runT P ONES lt Dig P.L := rfl

/-- What a slot with digits `dg` computes in `t` letters (no reduction). -/
def semN (lt : ℕ → ℕ → Let) (dg : ℕ → ℕ) : ℕ → St
  | 0 => ⟨1, 0, 0, 1, 0⟩
  | t + 1 => mulSt (semN lt dg t) (lt t (dg t))

theorem run_sound (P : Prm) (hv : P.valid) {ONES : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) {Dig : ℕ} {F : ℕ → ℕ} (hDig : Dig = pkF P.w F P.N)
    (hF : ∀ j < P.N, F j < 2 ^ P.w) :
    ∀ t ≤ P.L, (runT P ONES lt Dig t).2 = true → ∃ xs, Rep P (runT P ONES lt Dig t).1 xs ∧
      ∀ j < P.N, (∀ t' < t, digit (F j) t' < P.Δ) ∧ MEq P.p P.n (xs j) (semN lt (digit (F j)) t) := by
  have hp2 : 2 ≤ P.p := hv.2.2.2.1
  have hn2 : 2 ≤ P.n := hv.2.2.2.2.1
  intro t
  induction t with
  | zero =>
    intro _ _
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    refine ⟨fun _ => ⟨1, 0, 0, 1, 0⟩, ⟨hO, h0, h0, hO, h0, fun j _ => ⟨by simp; omega, by simp; omega,
      by simp; omega, by simp; omega, by simp; omega⟩⟩, fun j _ => ⟨fun t' h => absurd h (by omega), ?_⟩⟩
    exact ⟨Nat.ModEq.refl _, Nat.ModEq.refl _, Nat.ModEq.refl _, Nat.ModEq.refl _, Nat.ModEq.refl _⟩
  | succ t ih =>
    intro ht hok
    have e : runT P ONES lt Dig (t + 1) =
        ((stepP P ONES lt Dig t (runT P ONES lt Dig t).1).1,
          (runT P ONES lt Dig t).2 && (stepP P ONES lt Dig t (runT P ONES lt Dig t).1).2) := rfl
    rw [e] at hok ⊢
    simp only [Bool.and_eq_true] at hok
    obtain ⟨xs, hX, hxs⟩ := ih (by omega) hok.1
    obtain ⟨ys, hY, hys⟩ := step_sound P hv hO hlt hDig hF (by omega) hX hok.2
    refine ⟨ys, hY, fun j hj => ⟨fun t' h => ?_, ?_⟩⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
      · exact (hxs j hj).1 t' h
      · subst h; exact (hys j hj).1
    · exact (hys j hj).2.trans ((hxs j hj).2.mulSt _)

/-- Field `j` of the certificate number. -/
def fld (w Dig j : ℕ) : ℕ := Dig / 2 ^ (w * j) % 2 ^ w

/-- **Soundness of a batch.** Each slot's word (digits of field `j`) reaches the targets. -/
theorem batch_sound (P : Prm) (hv : P.valid) {ONES : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) {Dig : ℕ} {kind : Bool} {TA TB TC TD TZ : ℕ}
    {ta tb tc td tz : ℕ → ℕ} (hTA : TA = pkF P.w ta P.N) (hTB : TB = pkF P.w tb P.N)
    (hTC : TC = pkF P.w tc P.N) (hTD : TD = pkF P.w td P.N) (hTZ : TZ = pkF P.w tz P.N)
    (htb : ∀ j < P.N, ta j < 2 ^ P.w ∧ tb j < 2 ^ P.w ∧ tc j < 2 ^ P.w ∧ td j < 2 ^ P.w ∧ tz j < 2 ^ P.w)
    (h : batchOK P ONES lt Dig kind TA TB TC TD TZ = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semN lt (digit (fld P.w Dig j)) P.L).a ≡ ta j [MOD P.p] ∧
      (semN lt (digit (fld P.w Dig j)) P.L).c ≡ tc j [MOD P.p] ∧
      (semN lt (digit (fld P.w Dig j)) P.L).z ≡ tz j [MOD P.n] ∧
      (kind = true → (semN lt (digit (fld P.w Dig j)) P.L).b ≡ tb j [MOD P.p]) ∧
      (kind = false → (semN lt (digit (fld P.w Dig j)) P.L).d ≡ td j [MOD P.p]) := by
  have hw : 0 < P.w := by have := hv.1; omega
  have hpw : P.p ≤ 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.1
    have h2 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    nlinarith [hv.2.2.2.1]
  have hnw : P.n ≤ 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h2 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  unfold batchOK at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hlt0, ⟨⟨⟨hok, hA⟩, hC⟩, hZ⟩, hK⟩ := h
  have hDig : Dig = pkF P.w (fun j => fld P.w Dig j) P.N := (pkF_fields hw Dig hlt0).symm
  have hF : ∀ j < P.N, fld P.w Dig j < 2 ^ P.w := fun j _ => Nat.mod_lt _ (by positivity)
  rw [runP_eq] at hok hA hC hZ hK
  obtain ⟨xs, hX, hxs⟩ := run_sound P hv hO hlt hDig hF P.L (le_refl _) hok
  obtain ⟨hXa, hXb, hXc, hXd, hXz, hxb⟩ := hX
  have inj := fun {f g : ℕ → ℕ} (hf : ∀ j < P.N, f j < 2 ^ P.w) (hg : ∀ j < P.N, g j < 2 ^ P.w)
    (he : pkF P.w f P.N = pkF P.w g P.N) => pkF_inj hw hf hg he
  have ea := inj (fun j hj => lt_of_lt_of_le (hxb j hj).1 hpw) (fun j hj => (htb j hj).1) (hXa.symm.trans (hA.trans hTA))
  have ec := inj (fun j hj => lt_of_lt_of_le (hxb j hj).2.2.1 hpw) (fun j hj => (htb j hj).2.2.1)
    (hXc.symm.trans (hC.trans hTC))
  have ez := inj (fun j hj => lt_of_lt_of_le (hxb j hj).2.2.2.2 hnw) (fun j hj => (htb j hj).2.2.2.2)
    (hXz.symm.trans (hZ.trans hTZ))
  intro j hj
  obtain ⟨hdig, hma, hmb, hmc, hmd, hmz⟩ := hxs j hj
  refine ⟨hdig, (ea j hj) ▸ hma.symm, (ec j hj) ▸ hmc.symm, (ez j hj) ▸ hmz.symm, fun hk => ?_, fun hk => ?_⟩
  · subst hk
    simp only [cond_true, Nat.beq_eq] at hK
    have eb := inj (fun j hj => lt_of_lt_of_le (hxb j hj).2.1 hpw) (fun j hj => (htb j hj).2.1)
      (hXb.symm.trans (hK.trans hTB))
    exact (eb j hj) ▸ hmb.symm
  · subst hk
    simp only [cond_false, Nat.beq_eq] at hK
    have ed := inj (fun j hj => lt_of_lt_of_le (hxb j hj).2.2.2.1 hpw) (fun j hj => (htb j hj).2.2.2.1)
      (hXd.symm.trans (hK.trans hTD))
    exact (ed j hj) ▸ hmd.symm

end BipartiteDD.LeanAll.HaarSwar2
