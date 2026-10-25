import BipartiteDD.LeanAll.HaarSL
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.Subgroup.Center

/-! # Haar graphs of `PSL(2, p) × Z_n` from batch certificates

`PSL(2, p) × Z_n` is the quotient of `SL(2, p) × Z_n` by `{(±1, 0)}`. A word in the lifted generators covers an
element `x` of the quotient as soon as its product in `SL(2, p) × Z_n` is `x̃` or `-x̃` for a lift `x̃`. So batches run
over the sign-normalised matrices only (`c` in `1 … (p-1)/2`, or `c = 0` and `a` in `1 … (p-1)/2`), and the final
comparison accepts both signs: with the fieldwise masks `E₁ = [C = c]`, `E₂ = [C = p - c]` (or the same on `A` when
`c = 0`) it checks `E₁ + E₂ = 1` and that the other entries are the targets or their negatives accordingly
(`batchOKpm`, `batch_sound_pm`). -/

namespace BipartiteDD.LeanAll.HaarPSL

open BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.Swar Matrix

/-! ## Fieldwise comparisons -/

section Masks

variable (P : Prm) (ONES : ℕ)

/-- `[field ≥ q]`, for fields below `2 ^ (w-1)`. -/
def geM (q V : ℕ) : ℕ := ((V + (2 ^ (P.w - 1) - q) * ONES) >>> (P.w - 1)) &&& ONES

/-- `[field = q]`. -/
def eqM (q V : ℕ) : ℕ := geM P ONES q V - geM P ONES (q + 1) V

/-- A field mask made full (`0` or `2 ^ w - 1`). -/
def full (E : ℕ) : ℕ := E * (2 ^ P.w - 1)

end Masks

variable {N : ℕ}

theorem geM_eq (P : Prm) (hw : 1 ≤ P.w) {ONES V : ℕ} (hO : ONES = pkF P.w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF P.w v N) (hb : ∀ j < N, v j < 2 ^ (P.w - 1)) {q : ℕ} (hq : q ≤ 2 ^ (P.w - 1)) :
    geM P ONES q V = pkF P.w (fun j => if q ≤ v j then 1 else 0) N := by
  have hs := two_pow_split hw
  have e1 : V + (2 ^ (P.w - 1) - q) * ONES = pkF P.w (fun j => v j + (2 ^ (P.w - 1) - q)) N := by
    rw [hV, hO, ← pkF_mul, pkF_add]; simp
  have h2 : (1 : ℕ) < 2 ^ (P.w - (P.w - 1)) := by
    rw [show P.w - (P.w - 1) = 1 by omega]; norm_num
  unfold geM
  rw [e1, hO, pkF_shr_land (by omega) (by omega) h2 (fun j hj => by have := hb j hj; omega)]
  apply pkF_congr
  intro j hj
  rw [shr_land_one_half P.w _ hw (by have := hb j hj; omega)]
  have := hb j hj
  split_ifs <;> omega

theorem eqM_eq (P : Prm) (hw : 1 ≤ P.w) {ONES V : ℕ} (hO : ONES = pkF P.w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF P.w v N) (hb : ∀ j < N, v j < 2 ^ (P.w - 1)) {q : ℕ} (hq : q + 1 ≤ 2 ^ (P.w - 1)) :
    eqM P ONES q V = pkF P.w (fun j => if v j = q then 1 else 0) N := by
  unfold eqM
  rw [geM_eq P hw hO hV hb (by omega), geM_eq P hw hO hV hb hq, ← pkF_sub]
  · apply pkF_congr
    intro j _
    split_ifs <;> omega
  · intro j _
    split_ifs <;> omega

theorem full_land (P : Prm) {V E : ℕ} {v e : ℕ → ℕ} (hw : 0 < P.w) (hV : V = pkF P.w v N)
    (hE : E = pkF P.w e N) (hv : ∀ j < N, v j < 2 ^ P.w) (he : ∀ j < N, e j ≤ 1) :
    V &&& full P E = pkF P.w (fun j => if e j = 1 then v j else 0) N := by
  unfold full
  rw [hE, mul_comm, ← pkF_mul, hV, pkF_land hw hv (fun j hj => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (he j hj) with h | h <;> simp [h])]
  apply pkF_congr
  intro j hj
  rw [show (2 ^ P.w - 1) * e j = e j * (2 ^ P.w - 1) by ring, land_full _ _ (hv j hj) _ (he j hj)]

/-! ## The sign-insensitive batch check -/

/-- Kind `false` (`c ≠ 0`): `C` is `c` or `-c` per slot, and `A`, `D` follow the same sign (`D` against the ramp `RD`
or its negative `NRD`). Kind `true` (`c = 0`): `A` is `a` or `-a`, `C = 0`, and `B` follows. Always `Z = RZ`. -/
def batchOKpm (P : Prm) (ONES : ℕ) (lt : ℕ → ℕ → Let) (Dig : ℕ) (kind : Bool) (a c RD NRD RZ : ℕ) : Bool :=
  Nat.blt Dig (2 ^ (P.w * P.N)) &&
    ((runP P ONES lt Dig).2 && Nat.beq (runP P ONES lt Dig).1.z RZ &&
      cond kind
        (Nat.beq (eqM P ONES a (runP P ONES lt Dig).1.a + eqM P ONES ((P.p - a) % P.p) (runP P ONES lt Dig).1.a) ONES &&
          Nat.beq (runP P ONES lt Dig).1.c 0 &&
          Nat.beq (runP P ONES lt Dig).1.b ((RD &&& full P (eqM P ONES a (runP P ONES lt Dig).1.a)) +
            (NRD &&& full P (eqM P ONES ((P.p - a) % P.p) (runP P ONES lt Dig).1.a))))
        (Nat.beq (eqM P ONES c (runP P ONES lt Dig).1.c + eqM P ONES ((P.p - c) % P.p) (runP P ONES lt Dig).1.c) ONES &&
          Nat.beq (runP P ONES lt Dig).1.a (a * eqM P ONES c (runP P ONES lt Dig).1.c +
            ((P.p - a) % P.p) * eqM P ONES ((P.p - c) % P.p) (runP P ONES lt Dig).1.c) &&
          Nat.beq (runP P ONES lt Dig).1.d ((RD &&& full P (eqM P ONES c (runP P ONES lt Dig).1.c)) +
            (NRD &&& full P (eqM P ONES ((P.p - c) % P.p) (runP P ONES lt Dig).1.c)))))

theorem pick3 {xa xc xd a c c' a' d d' : ℕ}
    (e1 : (if xc = c then 1 else 0) + (if xc = c' then 1 else 0) = 1)
    (e2 : xa = a * (if xc = c then 1 else 0) + a' * (if xc = c' then 1 else 0))
    (e3 : xd = (if (if xc = c then 1 else 0) = 1 then d else 0) + (if (if xc = c' then 1 else 0) = 1 then d' else 0)) :
    (xa = a ∧ xc = c ∧ xd = d) ∨ (xa = a' ∧ xc = c' ∧ xd = d') := by
  by_cases h1 : xc = c <;> by_cases h2 : xc = c'
  · rw [if_pos h1, if_pos h2] at e1; omega
  · left; rw [if_pos h1, if_neg h2] at e2 e3; simp at e2 e3; exact ⟨e2, h1, e3⟩
  · right; rw [if_neg h1, if_pos h2] at e2 e3; simp at e2 e3; exact ⟨e2, h2, e3⟩
  · rw [if_neg h1, if_neg h2] at e1; omega

theorem pick2 {xa xb a a' d d' : ℕ}
    (e1 : (if xa = a then 1 else 0) + (if xa = a' then 1 else 0) = 1)
    (e3 : xb = (if (if xa = a then 1 else 0) = 1 then d else 0) + (if (if xa = a' then 1 else 0) = 1 then d' else 0)) :
    (xa = a ∧ xb = d) ∨ (xa = a' ∧ xb = d') := by
  by_cases h1 : xa = a <;> by_cases h2 : xa = a'
  · rw [if_pos h1, if_pos h2] at e1; omega
  · left; rw [if_pos h1, if_neg h2] at e3; simp at e3; exact ⟨h1, e3⟩
  · right; rw [if_neg h1, if_pos h2] at e3; simp at e3; exact ⟨h2, e3⟩
  · rw [if_neg h1, if_neg h2] at e1; omega

theorem ind_sum {x y : ℕ} {e1 e2 : ℕ} (he1 : e1 = (if x = y then 1 else 0)) (h : e1 + e2 = 1) :
    (x = y ∧ e1 = 1 ∧ e2 = 0) ∨ (x ≠ y ∧ e1 = 0 ∧ e2 = 1) := by
  by_cases hxy : x = y
  · left; simp [hxy] at he1; omega
  · right; simp [hxy] at he1; omega

set_option maxHeartbeats 2000000 in
/-- **Soundness of a sign-insensitive batch.** -/
theorem batch_sound_pm (P : Prm) (hv : P.valid) {ONES : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) {Dig : ℕ} {kind : Bool} {a c RD NRD RZ : ℕ} (ha : a < P.p)
    (hc : c < P.p) (hRD : RD = pkF P.w (fun j => j / P.n) P.N)
    (hNRD : NRD = pkF P.w (fun j => (P.p - j / P.n) % P.p) P.N) (hRZ : RZ = pkF P.w (fun j => j % P.n) P.N)
    (hNp : P.N = P.p * P.n) (h : batchOKpm P ONES lt Dig kind a c RD NRD RZ = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semN lt (digit (fld P.w Dig j)) P.L).z ≡ j % P.n [MOD P.n] ∧
      (kind = false →
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ a [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ c [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).d ≡ j / P.n [MOD P.p]) ∨
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ (P.p - a) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ (P.p - c) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).d ≡ (P.p - j / P.n) % P.p [MOD P.p])) ∧
      (kind = true →
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ a [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ 0 [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).b ≡ j / P.n [MOD P.p]) ∨
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ (P.p - a) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ 0 [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).b ≡ (P.p - j / P.n) % P.p [MOD P.p])) := by
  have hw8 := hv.1
  have hw : 0 < P.w := by omega
  have hw1 : 1 ≤ P.w := by omega
  have hs := two_pow_split hw1
  have hp2 : 2 ≤ P.p := hv.2.2.2.1
  have hn2 : 2 ≤ P.n := hv.2.2.2.2.1
  have hpH : 2 * P.p * P.p ≤ 2 ^ (P.w - 1) := hv.2.2.2.2.2.2.1
  have hnH : 2 * P.n ≤ 2 ^ (P.w - 1) := hv.2.2.2.2.2.2.2.1
  have hpH' : P.p + 1 ≤ 2 ^ (P.w - 1) := by nlinarith
  have h4 : 4 ≤ 2 ^ P.w := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold batchOKpm at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hlt0, ⟨hok, hZ⟩, hK⟩ := h
  have hDig : Dig = pkF P.w (fun j => fld P.w Dig j) P.N := (pkF_fields hw Dig hlt0).symm
  have hF : ∀ j < P.N, fld P.w Dig j < 2 ^ P.w := fun j _ => Nat.mod_lt _ (by positivity)
  rw [runP_eq] at hok hZ hK
  obtain ⟨xs, hX, hxs⟩ := run_sound P hv hO hlt hDig hF P.L (le_refl _) hok
  obtain ⟨hXa, hXb, hXc, hXd, hXz, hxb⟩ := hX
  have hbH : ∀ j < P.N, (xs j).a < 2 ^ (P.w - 1) ∧ (xs j).b < 2 ^ (P.w - 1) ∧ (xs j).c < 2 ^ (P.w - 1) ∧
      (xs j).d < 2 ^ (P.w - 1) := fun j hj => by
    have := hxb j hj; refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hW : ∀ j < P.N, (xs j).a < 2 ^ P.w ∧ (xs j).b < 2 ^ P.w ∧ (xs j).c < 2 ^ P.w ∧ (xs j).d < 2 ^ P.w ∧
      (xs j).z < 2 ^ P.w := fun j hj => by
    have := hbH j hj; have := hxb j hj; refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> omega
  have hjn : ∀ j < P.N, j / P.n < P.p := fun j hj =>
    (Nat.div_lt_iff_lt_mul (by omega)).2 (by rw [← hNp]; exact hj)
  -- the Z part
  have ez := pkF_inj hw (fun j hj => (hW j hj).2.2.2.2) (fun j hj => by have := Nat.mod_lt j (show 0 < P.n by omega); omega)
    (hXz.symm.trans (hZ.trans hRZ))
  intro j hj
  obtain ⟨hdg, hma, hmb, hmc, hmd, hmz⟩ := hxs j hj
  refine ⟨hdg, (ez j hj) ▸ hmz.symm, ?_, ?_⟩
  · -- kind false
    intro hk
    subst hk
    simp only [cond_false, Bool.and_eq_true, Nat.beq_eq] at hK
    obtain ⟨⟨hE, hA⟩, hD⟩ := hK
    have hE1 := eqM_eq P hw1 hO hXc (fun j hj => (hbH j hj).2.2.1) (q := c) (by omega)
    have hE2 := eqM_eq P hw1 hO hXc (fun j hj => (hbH j hj).2.2.1) (q := (P.p - c) % P.p)
      (by have := Nat.mod_lt (P.p - c) (show 0 < P.p by omega); omega)
    rw [hE1, hE2, ← pkF_add, hO] at hE
    have e1 := pkF_inj hw (fun j _ => by split_ifs <;> omega) (fun _ _ => by omega) hE j hj
    rw [hE1, hE2, ← pkF_mul, ← pkF_mul, ← pkF_add] at hA
    have e2 := pkF_inj hw (fun j hj => (hW j hj).1) (fun j _ => by
      have := Nat.mod_lt (P.p - a) (show 0 < P.p by omega)
      split_ifs <;> (try simp only [mul_one, mul_zero, add_zero, zero_add]) <;> omega) (hXa.symm.trans hA) j hj
    try simp only at e2
    rw [hE1, hE2, full_land P hw hRD rfl (fun j hj => by have := hjn j hj; omega)
      (fun j _ => by split_ifs <;> simp), full_land P hw hNRD rfl (fun j hj => by
        have := Nat.mod_lt (P.p - j / P.n) (show 0 < P.p by omega); omega)
      (fun j _ => by split_ifs <;> simp), ← pkF_add] at hD
    have e3 := pkF_inj hw (fun j hj => (hW j hj).2.2.2.1) (fun j hj => by
      have := Nat.mod_lt (P.p - j / P.n) (show 0 < P.p by omega); have := hjn j hj
      split_ifs <;> (try simp only [mul_one, mul_zero, add_zero, zero_add]) <;> omega) (hXd.symm.trans hD) j hj
    try simp only at e3
    rcases pick3 e1 e2 e3 with ⟨ha', hc', hd'⟩ | ⟨ha', hc', hd'⟩
    · left
      exact ⟨ha' ▸ hma.symm, hc' ▸ hmc.symm, hd' ▸ hmd.symm⟩
    · right
      exact ⟨ha' ▸ hma.symm, hc' ▸ hmc.symm, hd' ▸ hmd.symm⟩
  · -- kind true
    intro hk
    subst hk
    simp only [cond_true, Bool.and_eq_true, Nat.beq_eq] at hK
    obtain ⟨⟨hE, hC⟩, hB⟩ := hK
    have hE1 := eqM_eq P hw1 hO hXa (fun j hj => (hbH j hj).1) (q := a) (by omega)
    have hE2 := eqM_eq P hw1 hO hXa (fun j hj => (hbH j hj).1) (q := (P.p - a) % P.p)
      (by have := Nat.mod_lt (P.p - a) (show 0 < P.p by omega); omega)
    rw [hE1, hE2, ← pkF_add, hO] at hE
    have e1 := pkF_inj hw (fun j _ => by split_ifs <;> omega) (fun _ _ => by omega) hE j hj
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    have ec := pkF_inj hw (fun j hj => (hW j hj).2.2.1) (fun _ _ => by positivity) (hXc.symm.trans (hC.trans h0)) j hj
    rw [hE1, hE2, full_land P hw hRD rfl (fun j hj => by have := hjn j hj; omega)
      (fun j _ => by split_ifs <;> simp), full_land P hw hNRD rfl (fun j hj => by
        have := Nat.mod_lt (P.p - j / P.n) (show 0 < P.p by omega); omega)
      (fun j _ => by split_ifs <;> simp), ← pkF_add] at hB
    have e3 := pkF_inj hw (fun j hj => (hW j hj).2.1) (fun j hj => by
      have := Nat.mod_lt (P.p - j / P.n) (show 0 < P.p by omega); have := hjn j hj
      split_ifs <;> (try simp only [mul_one, mul_zero, add_zero, zero_add]) <;> omega) (hXb.symm.trans hB) j hj
    try simp only at e3
    rcases pick2 e1 e3 with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · left
      exact ⟨ha' ▸ hma.symm, ec ▸ hmc.symm, hb' ▸ hmb.symm⟩
    · right
      exact ⟨ha' ▸ hma.symm, ec ▸ hmc.symm, hb' ▸ hmb.symm⟩

/-! ## The group `PSL(2, p) × Z_n` -/

section Group

variable {p n : ℕ}

/-- `-1` in `SL(2, p)`. -/
def negOne : SpecialLinearGroup (Fin 2) (ZMod p) :=
  ⟨-1, by rw [det_neg]; simp⟩

theorem negOne_entries : negOne (p := p) 0 0 = -1 ∧ negOne (p := p) 0 1 = 0 ∧ negOne (p := p) 1 0 = 0 ∧
    negOne (p := p) 1 1 = -1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [negOne]

/-- The central element `(-1, 0)`. -/
def gneg : G p n := (negOne, 1)

theorem gneg_comm (y : G p n) : y * gneg = gneg * y := by
  refine Prod.ext ?_ (by simp [gneg])
  show y.1 * negOne = negOne * y.1
  apply Subtype.ext
  show y.1.1 * (-1) = (-1) * y.1.1
  simp

theorem gneg_sq : (gneg : G p n) ^ 2 = 1 := by
  rw [sq]
  refine Prod.ext ?_ (by simp [gneg])
  show negOne * negOne = (1 : SpecialLinearGroup (Fin 2) (ZMod p))
  apply Subtype.ext
  show (-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) * (-1) = 1
  simp

theorem gneg_ne [hp : Fact p.Prime] (hp2 : p ≠ 2) : (gneg : G p n) ≠ 1 := by
  intro h
  have h1 : ((gneg : G p n).1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
      ((1 : G p n).1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by rw [h]
  have h1' : (-1 : ZMod p) = 1 := by simpa [gneg, negOne] using h1
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    have e : ((2 : ℕ) : ZMod p) = 1 - (-1) := by push_cast; ring
    rw [e, h1', sub_self]
  rw [ZMod.natCast_eq_zero_iff] at h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)

/-- The subgroup `{(±1, 0)}`. -/
def Zc : Subgroup (G p n) := Subgroup.zpowers gneg

instance Zc_normal : (Zc (p := p) (n := n)).Normal :=
  Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 (Subgroup.mem_center_iff.2 gneg_comm))

/-- `PSL(2, p) × Z_n`. -/
abbrev PG (p n : ℕ) := G p n ⧸ (Zc (p := p) (n := n))

theorem card_PG [hp : Fact p.Prime] [NeZero n] (hp2 : p ≠ 2) :
    Nat.card (PG p n) * 2 = p * (p * p - 1) * n := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Zc (p := p) (n := n))
  have h2 : Nat.card (Zc (p := p) (n := n)) = 2 := by
    rw [Zc, Nat.card_zpowers]
    exact orderOf_eq_prime gneg_sq (gneg_ne hp2)
  rw [h2, Nat.card_eq_fintype_card (α := G p n), card_G (p := p) (n := n)] at h1
  exact h1.symm

/-- The quotient map. -/
abbrev pi : G p n →* PG p n := QuotientGroup.mk' Zc

theorem pi_gneg : pi (gneg : G p n) = 1 := (QuotientGroup.eq_one_iff (N := Zc) gneg).2 (Subgroup.mem_zpowers _)

theorem pi_gneg_mul (x : G p n) : pi (gneg * x) = pi x := by
  rw [map_mul, pi_gneg, one_mul]

theorem gneg_mul_entries (x : G p n) (i j : Fin 2) : (gneg * x).1 i j = -(x.1 i j) := by
  show ((-1 : Matrix (Fin 2) (Fin 2) (ZMod p)) * x.1.1) i j = _
  simp

theorem gneg_mul_snd (x : G p n) : (gneg * x).2 = x.2 := by simp [gneg]

theorem gneg_gneg (x : G p n) : gneg * (gneg * x) = x := by
  rw [← mul_assoc, ← sq, gneg_sq, one_mul]

theorem eq_of_entries_c [Fact p.Prime] {W X : SpecialLinearGroup (Fin 2) (ZMod p)} (hc : X 1 0 ≠ 0)
    (h00 : W 0 0 = X 0 0) (h10 : W 1 0 = X 1 0) (h11 : W 1 1 = X 1 1) : W = X := by
  have hW := det_entries W
  have hX := det_entries X
  rw [h00, h10, h11] at hW
  have h01 : W 0 1 = X 0 1 := by
    have : (W 0 1 - X 0 1) * X 1 0 = 0 := by linear_combination hX - hW
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  apply SpecialLinearGroup.ext
  intro i j; fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem eq_of_entries_nc [Fact p.Prime] {W X : SpecialLinearGroup (Fin 2) (ZMod p)} (hc : X 1 0 = 0)
    (h00 : W 0 0 = X 0 0) (h01 : W 0 1 = X 0 1) (h10 : W 1 0 = 0) : W = X := by
  have hW := det_entries W
  have hX := det_entries X
  rw [h00, h01, h10] at hW
  rw [hc] at hX
  have h11 : W 1 1 = X 1 1 := by
    have : X 0 0 * (W 1 1 - X 1 1) = 0 := by linear_combination hW - hX
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (a_ne_of_c X hc)
    · exact sub_eq_zero.mp h
  apply SpecialLinearGroup.ext
  intro i j; fin_cases i <;> fin_cases j
  exacts [h00, h01, h10.trans hc.symm, h11]

end Group

/-! ## Batches over sign-normalised matrices, and the cover -/

/-- `(p - 1) / 2`. -/
def hP (p : ℕ) : ℕ := (p - 1) / 2

def kindBp (p b : ℕ) : Bool := Nat.ble (p * hP p) b

def aBp (p b : ℕ) : ℕ := cond (kindBp p b) (b - p * hP p + 1) (b / hP p)

def cBp (p b : ℕ) : ℕ := cond (kindBp p b) 0 (b % hP p + 1)

/-- All `(p² - 1) / 2` batches pass. -/
def BatchesOKpm (P : Prm) (ONES RD NRD RZ : ℕ) (lt : ℕ → ℕ → Let) : Prop :=
  ∀ b < P.p * hP P.p + hP P.p, ∃ Dig, batchOKpm P ONES lt Dig (kindBp P.p b) (aBp P.p b) (cBp P.p b) RD NRD RZ = true

theorem batp_nc {p a : ℕ} (h1 : 1 ≤ hP p) (ha1 : 1 ≤ a) (ha : a ≤ hP p) :
    kindBp p (p * hP p + (a - 1)) = true ∧ aBp p (p * hP p + (a - 1)) = a ∧
      p * hP p + (a - 1) < p * hP p + hP p := by
  have hk : kindBp p (p * hP p + (a - 1)) = true := by unfold kindBp; rw [Nat.ble_eq]; omega
  refine ⟨hk, ?_, by omega⟩
  unfold aBp; rw [hk, cond_true]; omega

theorem batp_c {p a c : ℕ} (h1 : 1 ≤ hP p) (ha : a < p) (hc1 : 1 ≤ c) (hc : c ≤ hP p) :
    kindBp p (a * hP p + (c - 1)) = false ∧ aBp p (a * hP p + (c - 1)) = a ∧ cBp p (a * hP p + (c - 1)) = c ∧
      a * hP p + (c - 1) < p * hP p + hP p := by
  have hlt : a * hP p + (c - 1) < p * hP p := by
    calc a * hP p + (c - 1) < a * hP p + hP p := by omega
      _ = (a + 1) * hP p := by ring
      _ ≤ p * hP p := Nat.mul_le_mul_right _ ha
  have hk : kindBp p (a * hP p + (c - 1)) = false := by
    unfold kindBp
    exact Bool.eq_false_iff.mpr (fun h => absurd (Nat.le_of_ble_eq_true h) (by omega))
  refine ⟨hk, ?_, ?_, by omega⟩
  · unfold aBp; rw [hk, cond_false, Nat.add_comm (a * hP p), Nat.add_mul_div_right _ _ (by omega),
      Nat.div_eq_of_lt (by omega), Nat.zero_add]
  · unfold cBp; rw [hk, cond_false, Nat.add_comm (a * hP p), Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
    omega

section Cover

variable {p n : ℕ} (sG : ℕ → G p n) (invAt : ℕ → Bool)

theorem cast_negmod {q k : ℕ} (hk : k ≤ q) : (((q - k) % q : ℕ) : ZMod q) = -(k : ZMod q) := by
  rw [ZMod.natCast_mod, cast_sub_of_le hk]

/-- **The cover, up to sign.** If all sign-normalised batches pass, every element `x` has a word whose product is
`x` or `(-1, 0) x`. -/
theorem cover_of_batches_pm [hp : Fact p.Prime] [NeZero n] (hp2 : p ≠ 2) (P : Prm) (hv : P.valid)
    (hpP : P.p = p) (hnP : P.n = n) (hN : P.N = p * n) {ONES RD NRD RZ : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (hRD : RD = pkF P.w (fun j => j / P.n) P.N)
    (hNRD : NRD = pkF P.w (fun j => (P.p - j / P.n) % P.p) P.N) (hRZ : RZ = pkF P.w (fun j => j % P.n) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) (hrep : LetRep sG invAt P.Δ P.L lt)
    (hB : BatchesOKpm P ONES RD NRD RZ lt) :
    ∀ x : G p n, ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧
      (wordG sG invAt dg P.L = x ∨ wordG sG invAt dg P.L = gneg * x) := by
  have h2 := p_two (p := p)
  have hp3 : 3 ≤ p := by omega
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hh : 2 * hP p + 1 = p := by unfold hP; omega
  have hh1 : 1 ≤ hP p := by unfold hP; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hNp : P.N = P.p * P.n := by rw [hN, hpP, hnP]
  -- the core: sign-normalised elements
  have core : ∀ x : G p n, ((x.1 1 0 ≠ 0 ∧ (x.1 1 0).val ≤ hP p) ∨ (x.1 1 0 = 0 ∧ (x.1 0 0).val ≤ hP p)) →
      ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧
        (wordG sG invAt dg P.L = x ∨ wordG sG invAt dg P.L = gneg * x) := by
    intro ⟨A, z⟩ hcan
    have hzv := ZMod.val_lt (Multiplicative.toAdd z)
    have hav := ZMod.val_lt (A 0 0)
    have hbv := ZMod.val_lt (A 0 1)
    have hcv := ZMod.val_lt (A 1 0)
    have hdv := ZMod.val_lt (A 1 1)
    rcases hcan with ⟨hc, hch⟩ | ⟨hc, hah⟩
    · -- `c ≠ 0`
      have hc1 := val_pos_of_ne hc
      obtain ⟨hbk, haB, hcB, hbl⟩ := batp_c hh1 hav hc1 hch
      obtain ⟨Dig, hDig⟩ := hB ((A 0 0).val * hP p + ((A 1 0).val - 1)) (by rw [hpP]; exact hbl)
      rw [hpP, hbk, haB, hcB] at hDig
      obtain ⟨j, hj⟩ : ∃ j, j = (A 1 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
      have hjN : j < P.N := by
        rw [hN]
        calc j < (A 1 1).val * n + n := by omega
          _ = ((A 1 1).val + 1) * n := by ring
          _ ≤ p * n := Nat.mul_le_mul_right _ hdv
      have hb := batch_sound_pm P hv hO hlt (by rw [hpP]; exact hav) (by rw [hpP]; exact hcv) hRD hNRD hRZ hNp
        hDig j hjN
      obtain ⟨hdg, mz, hkf, -⟩ := hb
      refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
      obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
      have hjd : j / n = (A 1 1).val := by
        rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
      have hjz : j % n = (Multiplicative.toAdd z).val := by
        rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
      simp only [hpP, hnP] at hkf mz
      have Wz : (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = z := by
        apply Multiplicative.toAdd.injective
        rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
      rcases hkf trivial with ⟨ma, mc, md⟩ | ⟨ma, mc, md⟩
      · left
        refine Prod.ext (eq_of_entries_c hc ?_ ?_ ?_) Wz
        · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
        · rw [← ec, cast_of_modEq mc, ZMod.natCast_zmod_val]
        · rw [← ed, cast_of_modEq md, hjd, ZMod.natCast_zmod_val]
      · right
        have hc' : (gneg * ((A, z) : G p n)).1 1 0 ≠ 0 := by rw [gneg_mul_entries]; exact neg_ne_zero.2 hc
        refine Prod.ext (eq_of_entries_c hc' ?_ ?_ ?_) (by rw [Wz, gneg_mul_snd])
        · rw [gneg_mul_entries, ← ea, cast_of_modEq ma, cast_negmod hav.le, ZMod.natCast_zmod_val]
        · rw [gneg_mul_entries, ← ec, cast_of_modEq mc, cast_negmod hcv.le, ZMod.natCast_zmod_val]
        · rw [gneg_mul_entries, ← ed, cast_of_modEq md, hjd, cast_negmod hdv.le, ZMod.natCast_zmod_val]
    · -- `c = 0`
      have ha1 := val_pos_of_ne (a_ne_of_c A hc)
      obtain ⟨hbk, haB, hbl⟩ := batp_nc hh1 ha1 hah
      obtain ⟨Dig, hDig⟩ := hB (p * hP p + ((A 0 0).val - 1)) (by rw [hpP]; exact hbl)
      rw [hpP, hbk, haB] at hDig
      obtain ⟨j, hj⟩ : ∃ j, j = (A 0 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
      have hjN : j < P.N := by
        rw [hN]
        calc j < (A 0 1).val * n + n := by omega
          _ = ((A 0 1).val + 1) * n := by ring
          _ ≤ p * n := Nat.mul_le_mul_right _ hbv
      have hb := batch_sound_pm P hv hO hlt (by rw [hpP]; exact hav)
        (c := cBp p (p * hP p + ((A 0 0).val - 1))) (by
          rw [hpP]; unfold cBp; rw [hbk, cond_true]; omega) hRD hNRD hRZ hNp
        hDig j hjN
      obtain ⟨hdg, mz, -, hkt⟩ := hb
      refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
      obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
      have hjb : j / n = (A 0 1).val := by
        rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
      have hjz : j % n = (Multiplicative.toAdd z).val := by
        rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
      simp only [hpP, hnP] at hkt mz
      have Wz : (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = z := by
        apply Multiplicative.toAdd.injective
        rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
      rcases hkt trivial with ⟨ma, mc, mb⟩ | ⟨ma, mc, mb⟩
      · left
        refine Prod.ext (eq_of_entries_nc hc ?_ ?_ ?_) Wz
        · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
        · rw [← eb, cast_of_modEq mb, hjb, ZMod.natCast_zmod_val]
        · rw [← ec, cast_of_modEq mc, Nat.cast_zero]
      · right
        have hc' : (gneg * ((A, z) : G p n)).1 1 0 = 0 := by rw [gneg_mul_entries, hc, neg_zero]
        refine Prod.ext (eq_of_entries_nc hc' ?_ ?_ ?_) (by rw [Wz, gneg_mul_snd])
        · rw [gneg_mul_entries, ← ea, cast_of_modEq ma, cast_negmod hav.le, ZMod.natCast_zmod_val]
        · rw [gneg_mul_entries, ← eb, cast_of_modEq mb, hjb, cast_negmod hbv.le, ZMod.natCast_zmod_val]
        · rw [← ec, cast_of_modEq mc, Nat.cast_zero]
  -- every element or its negative is sign-normalised
  intro x
  by_cases hcan : (x.1 1 0 ≠ 0 ∧ (x.1 1 0).val ≤ hP p) ∨ (x.1 1 0 = 0 ∧ (x.1 0 0).val ≤ hP p)
  · exact core x hcan
  · have hcan' : ((gneg * x).1 1 0 ≠ 0 ∧ ((gneg * x).1 1 0).val ≤ hP p) ∨
        ((gneg * x).1 1 0 = 0 ∧ ((gneg * x).1 0 0).val ≤ hP p) := by
      rw [gneg_mul_entries, gneg_mul_entries]
      push_neg at hcan
      by_cases hc : x.1 1 0 = 0
      · right
        refine ⟨by rw [hc, neg_zero], ?_⟩
        have ha := a_ne_of_c x.1 hc
        have h1 := hcan.2 hc
        rw [ZMod.neg_val, if_neg ha]
        have := ZMod.val_lt (x.1 0 0)
        omega
      · left
        refine ⟨neg_ne_zero.2 hc, ?_⟩
        have h1 := hcan.1 hc
        rw [ZMod.neg_val, if_neg hc]
        have := ZMod.val_lt (x.1 1 0)
        omega
    obtain ⟨dg, hdg, hw⟩ := core _ hcan'
    refine ⟨dg, hdg, ?_⟩
    rcases hw with hw | hw
    · exact Or.inr hw
    · exact Or.inl (hw.trans (gneg_gneg x))

end Cover

end BipartiteDD.LeanAll.HaarPSL
