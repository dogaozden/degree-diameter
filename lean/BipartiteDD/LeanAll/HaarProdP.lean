import BipartiteDD.LeanAll.HaarProd2

/-! # Haar graphs with a `PSL(2,q)` second factor: `PSL(2,p) × Z_n × PSL(2,q)`

As `HaarProd.lean`, with the second factor `PSL(2,q)`, written as `PG q 1` (`(SL(2,q) × Z_1) / {±1}`). A batch fixes
the sign-normalised second matrix `A₂` (batches `kindBp`, `aBp`, `cBp` of `HaarPSL`, free entry `jSp`) and runs over
the slots of the first factor. The second check is `batchOKpm` with constant targets: `batch_sound_pmg` is
`batch_sound_pm` for any free-entry targets `rd` (the ramp `j / n` there, the constant `jSp A₂` here), so every slot's
word has matrix `A₂` or `-A₂` in the second factor (`word_const_pm`), the same class in `PSL(2,q)`. `cover_prod_pp`
puts this together with `cover_of_batches_pm_ex` for the first factor. -/

namespace BipartiteDD.LeanAll.HaarProdP

open BipartiteDD.LeanAll.HaarSwar2 BipartiteDD.LeanAll.HaarSL2 BipartiteDD.LeanAll.HaarPSL2 BipartiteDD.LeanAll.HaarProd2
open BipartiteDD.LeanAll.Swar Matrix

set_option maxHeartbeats 2000000 in
/-- **Soundness of a sign-insensitive batch, any free-entry targets** (`batch_sound_pm` with `rd` in place of the
ramp `j / n`). -/
theorem batch_sound_pmg (P : Prm) (hv : P.valid) {ONES : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) {Dig : ℕ} {kind : Bool} {a c RD NRD RZ : ℕ} (ha : a < P.p)
    (hc : c < P.p) {rd : ℕ → ℕ} (hrd : ∀ j < P.N, rd j < P.p) (hRD : RD = pkF P.w rd P.N)
    (hNRD : NRD = pkF P.w (fun j => (P.p - rd j) % P.p) P.N) (hRZ : RZ = pkF P.w (fun j => j % P.n) P.N)
    (h : batchOKpm P ONES lt Dig kind a c RD NRD RZ = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semN lt (digit (fld P.w Dig j)) P.L).z ≡ j % P.n [MOD P.n] ∧
      (kind = false →
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ a [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ c [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).d ≡ rd j [MOD P.p]) ∨
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ (P.p - a) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ (P.p - c) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).d ≡ (P.p - rd j) % P.p [MOD P.p])) ∧
      (kind = true →
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ a [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ 0 [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).b ≡ rd j [MOD P.p]) ∨
        ((semN lt (digit (fld P.w Dig j)) P.L).a ≡ (P.p - a) % P.p [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).c ≡ 0 [MOD P.p] ∧
          (semN lt (digit (fld P.w Dig j)) P.L).b ≡ (P.p - rd j) % P.p [MOD P.p])) := by
  have hw8 := hv.1
  have hw : 0 < P.w := by omega
  have hw1 : 1 ≤ P.w := by omega
  have hs := two_pow_split hw1
  have hp2 : 2 ≤ P.p := hv.2.2.2.1
  have hn2 : 1 ≤ P.n := hv.2.2.2.2.1
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
  have hjn : ∀ j < P.N, rd j < P.p := hrd
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
        have := Nat.mod_lt (P.p - rd j) (show 0 < P.p by omega); omega)
      (fun j _ => by split_ifs <;> simp), ← pkF_add] at hD
    have e3 := pkF_inj hw (fun j hj => (hW j hj).2.2.2.1) (fun j hj => by
      have := Nat.mod_lt (P.p - rd j) (show 0 < P.p by omega); have := hjn j hj
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
        have := Nat.mod_lt (P.p - rd j) (show 0 < P.p by omega); omega)
      (fun j _ => by split_ifs <;> simp), ← pkF_add] at hB
    have e3 := pkF_inj hw (fun j hj => (hW j hj).2.1) (fun j hj => by
      have := Nat.mod_lt (P.p - rd j) (show 0 < P.p by omega); have := hjn j hj
      split_ifs <;> (try simp only [mul_one, mul_zero, add_zero, zero_add]) <;> omega) (hXb.symm.trans hB) j hj
    try simp only at e3
    rcases pick2 e1 e3 with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · left
      exact ⟨ha' ▸ hma.symm, ec ▸ hmc.symm, hb' ▸ hmb.symm⟩
    · right
      exact ⟨ha' ▸ hma.symm, ec ▸ hmc.symm, hb' ▸ hmb.symm⟩

/-! ## The second factor `PSL(2,q)` -/

section Second

variable {q : ℕ}

/-- Sign-normalised: `c` in `1 … h`, or `c = 0` and `a` in `1 … h` (`h = (q-1)/2`). -/
def Canon (x : G q 1) : Prop :=
  (x.1 1 0 ≠ 0 ∧ (x.1 1 0).val ≤ hP q) ∨ (x.1 1 0 = 0 ∧ (x.1 0 0).val ≤ hP q)

/-- The sign-normalised batch of `x` (as in `cover_of_batches_pm`). -/
noncomputable def bSp (x : G q 1) : ℕ :=
  if x.1 1 0 = 0 then q * hP q + ((x.1 0 0).val - 1) else (x.1 0 0).val * hP q + ((x.1 1 0).val - 1)

/-- The free entry of `x` in its batch: `b` if `c = 0`, else `d`. -/
noncomputable def jSp (x : G q 1) : ℕ := if x.1 1 0 = 0 then (x.1 0 1).val else (x.1 1 1).val

theorem jSp_lt [NeZero q] (x : G q 1) : jSp x < q := by
  unfold jSp; split_ifs <;> exact ZMod.val_lt _

theorem hP_pos [hq : Fact q.Prime] (hq2 : q ≠ 2) : 1 ≤ hP q := by
  have h2 := p_two (p := q)
  have hodd : q % 2 = 1 := by
    rcases hq.out.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  unfold hP; omega

theorem bSp_lt [hq : Fact q.Prime] (hq2 : q ≠ 2) {x : G q 1} (hx : Canon x) : bSp x < q * hP q + hP q := by
  have hh1 := hP_pos hq2
  unfold bSp
  rcases hx with ⟨hc, hch⟩ | ⟨hc, hah⟩
  · rw [if_neg hc]; exact (batp_c hh1 (ZMod.val_lt _) (val_pos_of_ne hc) hch).2.2.2
  · rw [if_pos hc]; exact (batp_nc hh1 (val_pos_of_ne (a_ne_of_c x.1 hc)) hah).2.2

/-- Every element of `PSL(2,q)` (as `PG q 1`) has a sign-normalised lift. -/
theorem canon_exists [hq : Fact q.Prime] (hq2 : q ≠ 2) (y : PG q 1) : ∃ x : G q 1, Canon x ∧ pi x = y := by
  obtain ⟨x, rfl⟩ := pi_surj y
  have h2 := p_two (p := q)
  have hodd : q % 2 = 1 := by
    rcases hq.out.eq_two_or_odd with h | h
    · exact absurd h hq2
    · exact h
  have hh : 2 * hP q + 1 = q := by unfold hP; omega
  by_cases hcan : Canon x
  · exact ⟨x, hcan, rfl⟩
  · refine ⟨gneg * x, ?_, pi_gneg_mul x⟩
    unfold Canon at hcan ⊢
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

/-- A word that meets the constant targets of `x`'s sign-normalised batch (either sign) at some slot has the class of
`x` in `PSL(2,q)`. -/
theorem word_const_pm [hq : Fact q.Prime] (hq2 : q ≠ 2) (sG : ℕ → G q 1) (invAt : ℕ → Bool) (P : Prm)
    (hv : P.valid) (hpP : P.p = q) {ONES RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    (hRZ : RZ = pkF P.w (fun j => j % P.n) P.N) {lt : ℕ → ℕ → Let} (hlt : LetOK P lt)
    (hrep : LetRep sG invAt P.Δ P.L lt) {x : G q 1} (hx : Canon x) {Dig : ℕ}
    (h : batchOKpm P ONES lt Dig (kindBp q (bSp x)) (aBp q (bSp x)) (cBp q (bSp x)) (jSp x * ONES)
      ((q - jSp x) % q * ONES) RZ = true) {j : ℕ} (hj : j < P.N) :
    pi (wordG sG invAt (digit (fld P.w Dig j)) P.L) = pi x := by
  have hh1 := hP_pos hq2
  have hav := ZMod.val_lt (x.1 0 0)
  have hbv := ZMod.val_lt (x.1 0 1)
  have hcv := ZMod.val_lt (x.1 1 0)
  have hdv := ZMod.val_lt (x.1 1 1)
  have hz : ∀ y y' : G q 1, y.2 = y'.2 := fun y y' => Subsingleton.elim _ _
  rcases hx with ⟨hc, hch⟩ | ⟨hc, hah⟩
  · obtain ⟨hbk, haB, hcB, -⟩ := batp_c hh1 hav (val_pos_of_ne hc) hch
    have eb : bSp x = (x.1 0 0).val * hP q + ((x.1 1 0).val - 1) := by unfold bSp; rw [if_neg hc]
    have ej : jSp x = (x.1 1 1).val := by unfold jSp; rw [if_neg hc]
    rw [eb, ej, hbk, haB, hcB] at h
    have hb := batch_sound_pmg P hv hO hlt (by rw [hpP]; exact hav) (by rw [hpP]; exact hcv)
      (rd := fun _ => (x.1 1 1).val) (fun _ _ => by rw [hpP]; exact hdv) (by rw [hO, ← pkF_const])
      (by rw [hO, ← pkF_const, hpP]) hRZ h j hj
    obtain ⟨hdg, -, hkf, -⟩ := hb
    obtain ⟨ea, -, ec, ed, -⟩ := semN_rep (p := q) (n := 1) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at hkf
    try dsimp only at hkf
    rcases hkf rfl with ⟨ma, mc, md⟩ | ⟨ma, mc, md⟩
    · have e : wordG sG invAt (digit (fld P.w Dig j)) P.L = x :=
        Prod.ext (eq_of_entries_c hc (by rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val])
          (by rw [← ec, cast_of_modEq mc, ZMod.natCast_zmod_val])
          (by rw [← ed, cast_of_modEq md, ZMod.natCast_zmod_val])) (hz _ _)
      rw [e]
    · have hc' : (gneg * x).1 1 0 ≠ 0 := by rw [gneg_mul_entries]; exact neg_ne_zero.2 hc
      have e : wordG sG invAt (digit (fld P.w Dig j)) P.L = gneg * x :=
        Prod.ext (eq_of_entries_c hc'
          (by rw [gneg_mul_entries, ← ea, cast_of_modEq ma, cast_negmod hav.le, ZMod.natCast_zmod_val])
          (by rw [gneg_mul_entries, ← ec, cast_of_modEq mc, cast_negmod hcv.le, ZMod.natCast_zmod_val])
          (by rw [gneg_mul_entries, ← ed, cast_of_modEq md, cast_negmod hdv.le, ZMod.natCast_zmod_val]))
          (hz _ _)
      rw [e, pi_gneg_mul]
  · have ha1 := val_pos_of_ne (a_ne_of_c x.1 hc)
    obtain ⟨hbk, haB, -⟩ := batp_nc hh1 ha1 hah
    have eb : bSp x = q * hP q + ((x.1 0 0).val - 1) := by unfold bSp; rw [if_pos hc]
    have ej : jSp x = (x.1 0 1).val := by unfold jSp; rw [if_pos hc]
    rw [eb, ej, hbk, haB] at h
    have hb := batch_sound_pmg P hv hO hlt (by rw [hpP]; exact hav)
      (c := cBp q (q * hP q + ((x.1 0 0).val - 1))) (by rw [hpP]; unfold cBp; rw [hbk, cond_true]; omega)
      (rd := fun _ => (x.1 0 1).val) (fun _ _ => by rw [hpP]; exact hbv) (by rw [hO, ← pkF_const])
      (by rw [hO, ← pkF_const, hpP]) hRZ h j hj
    obtain ⟨hdg, -, -, hkt⟩ := hb
    obtain ⟨ea, eb', ec, -, -⟩ := semN_rep (p := q) (n := 1) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at hkt
    try dsimp only at hkt
    rcases hkt rfl with ⟨ma, mc, mb⟩ | ⟨ma, mc, mb⟩
    · have e : wordG sG invAt (digit (fld P.w Dig j)) P.L = x :=
        Prod.ext (eq_of_entries_nc hc (by rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val])
          (by rw [← eb', cast_of_modEq mb, ZMod.natCast_zmod_val])
          (by rw [← ec, cast_of_modEq mc, Nat.cast_zero])) (hz _ _)
      rw [e]
    · have hc' : (gneg * x).1 1 0 = 0 := by rw [gneg_mul_entries, hc, neg_zero]
      have e : wordG sG invAt (digit (fld P.w Dig j)) P.L = gneg * x :=
        Prod.ext (eq_of_entries_nc hc'
          (by rw [gneg_mul_entries, ← ea, cast_of_modEq ma, cast_negmod hav.le, ZMod.natCast_zmod_val])
          (by rw [gneg_mul_entries, ← eb', cast_of_modEq mb, cast_negmod hbv.le, ZMod.natCast_zmod_val])
          (by rw [← ec, cast_of_modEq mc, Nat.cast_zero])) (hz _ _)
      rw [e, pi_gneg_mul]

end Second

/-! ## The product cover -/

section Prod

variable {p q n : ℕ}

theorem flat_index2 {B Q B2 b2 j2 b : ℕ} (hB : 0 < B) (hQ : 0 < Q) (hb2 : b2 < B2) (hj2 : j2 < Q) (hb : b < B) :
    ((b2 * Q + j2) * B + b) % B = b ∧ ((b2 * Q + j2) * B + b) / B / Q = b2 ∧
      ((b2 * Q + j2) * B + b) / B % Q = j2 ∧ (b2 * Q + j2) * B + b < B2 * Q * B := by
  have e1 : ((b2 * Q + j2) * B + b) / B = b2 * Q + j2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb, Nat.zero_add]
  refine ⟨by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb], ?_, ?_, ?_⟩
  · rw [e1, Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hj2, Nat.zero_add]
  · rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2]
  · have h1 : b2 * Q + j2 + 1 ≤ B2 * Q := by
      have : (b2 + 1) * Q ≤ B2 * Q := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    calc (b2 * Q + j2) * B + b < (b2 * Q + j2) * B + B := by omega
      _ = (b2 * Q + j2 + 1) * B := by ring
      _ ≤ B2 * Q * B := Nat.mul_le_mul_right _ h1

/-- **The cover of `PSL(2,p) × Z_n × PSL(2,q)`.** Batch `i` checks the first factor's sign-normalised batch
`i % B₁` (`B₁ = p h_p + h_p`) and the constant targets, up to sign, of the second factor's sign-normalised batch
`i / B₁ / q` with free entry `i / B₁ % q`. -/
theorem cover_prod_pp [Fact p.Prime] [hq : Fact q.Prime] [NeZero n] (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (sG₁ : ℕ → G p n) (sG₂ : ℕ → G q 1) (invAt : ℕ → Bool) (P₁ P₂ : Prm) (hv₁ : P₁.valid) (hv₂ : P₂.valid)
    (hpP : P₁.p = p) (hnP : P₁.n = n) (hN : P₁.N = p * n) (hqP : P₂.p = q) (hnP₂ : P₂.n = 1) (hN₂ : P₂.N = P₁.N)
    (hw₂ : P₂.w = P₁.w) (hΔ₂ : P₂.Δ = P₁.Δ) (hL₂ : P₂.L = P₁.L) {ONES RD NRD RZ RZ₂ : ℕ}
    (hO : ONES = pkF P₁.w (fun _ => 1) P₁.N) (hRD : RD = pkF P₁.w (fun j => j / P₁.n) P₁.N)
    (hNRD : NRD = pkF P₁.w (fun j => (P₁.p - j / P₁.n) % P₁.p) P₁.N) (hRZ : RZ = pkF P₁.w (fun j => j % P₁.n) P₁.N)
    (hRZ₂ : RZ₂ = pkF P₁.w (fun j => j % 1) P₁.N)
    {lt₁ lt₂ : ℕ → ℕ → Let} (hlt₁ : LetOK P₁ lt₁) (hlt₂ : LetOK P₂ lt₂)
    (hrep₁ : LetRep sG₁ invAt P₁.Δ P₁.L lt₁) (hrep₂ : LetRep sG₂ invAt P₂.Δ P₂.L lt₂)
    (hB : ∀ i < (q * hP q + hP q) * q * (p * hP p + hP p), ∃ Dig,
      batchOKpm P₁ ONES lt₁ Dig (kindBp p (i % (p * hP p + hP p))) (aBp p (i % (p * hP p + hP p)))
        (cBp p (i % (p * hP p + hP p))) RD NRD RZ = true ∧
      batchOKpm P₂ ONES lt₂ Dig (kindBp q (i / (p * hP p + hP p) / q)) (aBp q (i / (p * hP p + hP p) / q))
        (cBp q (i / (p * hP p + hP p) / q)) (i / (p * hP p + hP p) % q * ONES)
        ((q - i / (p * hP p + hP p) % q) % q * ONES) RZ₂ = true) :
    ∀ x : PG p n × PG q 1, ∃ dg : ℕ → ℕ, (∀ t < P₁.L, dg t < P₁.Δ) ∧
      wordX (fun u => (pi (sG₁ u), pi (sG₂ u))) invAt dg P₁.L = x := by
  intro ⟨y₁, y₂⟩
  obtain ⟨x₁, rfl⟩ := pi_surj y₁
  obtain ⟨x₂, hx₂, rfl⟩ := canon_exists hq2 y₂
  have hB0 : 0 < p * hP p + hP p := by
    have := hP_pos (q := p) hp2
    nlinarith
  have hcov := cover_of_batches_pm_ex sG₁ invAt hp2 P₁ hv₁ hpP hnP hN hO hRD hNRD hRZ hlt₁ hrep₁
    (fun Dig => batchOKpm P₂ ONES lt₂ Dig (kindBp q (bSp x₂)) (aBp q (bSp x₂)) (cBp q (bSp x₂)) (jSp x₂ * ONES)
      ((q - jSp x₂) % q * ONES) RZ₂ = true)
    (fun b hb => by
      rw [hpP] at hb ⊢
      obtain ⟨e1, e2, e3, e4⟩ := flat_index2 hB0 (Nat.pos_of_ne_zero (NeZero.ne q)) (bSp_lt hq2 hx₂) (jSp_lt x₂) hb
      have := hB _ e4
      rw [e1, e2, e3] at this
      exact this)
  obtain ⟨Dig, hE, j, hjN, hdg, hw⟩ := hcov x₁
  refine ⟨digit (fld P₁.w Dig j), hdg, ?_⟩
  rw [wordX_pair]
  refine Prod.ext ?_ ?_
  · show wordX (fun u => pi (sG₁ u)) invAt (digit (fld P₁.w Dig j)) P₁.L = pi x₁
    rw [← wordX_map sG₁ invAt pi, wordX_wordG]
    rcases hw with hw | hw
    · rw [hw]
    · rw [hw, pi_gneg_mul]
  · show wordX (fun u => pi (sG₂ u)) invAt (digit (fld P₁.w Dig j)) P₁.L = pi x₂
    rw [← wordX_map sG₂ invAt pi, wordX_wordG]
    have := word_const_pm hq2 sG₂ invAt P₂ hv₂ hqP (by rw [hO, hw₂, hN₂]) (by rw [hRZ₂, hw₂, hN₂, hnP₂]) hlt₂
      hrep₂ hx₂ hE (j := j) (by rw [hN₂]; exact hjN)
    rw [hw₂, hL₂] at this
    exact this

/-- The order of `PSL(2,p) × Z_n × PSL(2,q)`, four times. -/
theorem card_PG_PG [Fact p.Prime] [Fact q.Prime] [NeZero n] (hp2 : p ≠ 2) (hq2 : q ≠ 2) :
    Nat.card (PG p n × PG q 1) * 4 = p * (p * p - 1) * n * (q * (q * q - 1)) := by
  have h1 := card_PG (p := p) (n := n) hp2
  have h2 := card_PG (p := q) (n := 1) hq2
  rw [Nat.card_prod]
  calc Nat.card (PG p n) * Nat.card (PG q 1) * 4 = (Nat.card (PG p n) * 2) * (Nat.card (PG q 1) * 2) := by ring
    _ = _ := by rw [h1, h2]; ring

end Prod

end BipartiteDD.LeanAll.HaarProdP
