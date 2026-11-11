import BipartiteDD.LeanAll.HaarPSL2

/-! # Haar graphs of `SL(2,p) × Z_n × SL(2,q)` and `PSL(2,p) × Z_n × SL(2,q)` from batch certificates (copy of `HaarProd.lean` over `HaarPSL2.lean`)

A batch fixes the second matrix `A₂` and runs over the slots of the first factor exactly as for `SL(2,p) × Z_n`
(or `PSL(2,p) × Z_n`). The same certificate is checked twice: with the letters of the first factor against the
ramp targets, and with the letters of the second factor (same digits, same shifts) against the constant targets
of `A₂`. The second check uses the general `batch_sound` with constant targets (`word_const`). The covers of the
first factor are restated with an extra condition `E` on the certificate (`cover_of_batches_ex`,
`cover_of_batches_pm_ex`, the proofs of `cover_of_batches` and `cover_of_batches_pm` with the certificate kept). -/

namespace BipartiteDD.LeanAll.HaarProd2

open BipartiteDD.LeanAll.HaarSwar2 BipartiteDD.LeanAll.HaarSL2 BipartiteDD.LeanAll.HaarPSL2 BipartiteDD.LeanAll.Swar
open Matrix

/-! ## Words in any group -/

section Words

variable {K : Type*} [Group K] (s : ℕ → K) (invAt : ℕ → Bool)

/-- Letter `u` at step `t`. -/
def letterX (t u : ℕ) : K := cond (invAt t) (s u)⁻¹ (s u)

/-- The product of the first `t` letters of the word with digits `dg`. -/
def wordX (dg : ℕ → ℕ) : ℕ → K
  | 0 => 1
  | t + 1 => wordX dg t * letterX s invAt t (dg t)

theorem wordX_succ (dg : ℕ → ℕ) (t : ℕ) : wordX s invAt dg (t + 1) = wordX s invAt dg t * letterX s invAt t (dg t) :=
  rfl

/-- Pairs of letters `(s (dg (o + 2i)), s (dg (o + 2i + 1)))` for `i < k`. -/
def pairsX (dg : ℕ → ℕ) (o : ℕ) : ℕ → List (K × K)
  | 0 => []
  | k + 1 => pairsX dg o k ++ [(s (dg (o + 2 * k)), s (dg (o + 2 * k + 1)))]

theorem pairsX_mem {S : Finset K} {Δ : ℕ} (hS : ∀ u < Δ, s u ∈ S) (dg : ℕ → ℕ) (o : ℕ) :
    ∀ k, (∀ t < o + 2 * k, dg t < Δ) → ∀ q ∈ pairsX s dg o k, q.1 ∈ S ∧ q.2 ∈ S := by
  intro k
  induction k with
  | zero => intro _ q hq; simp [pairsX] at hq
  | succ k ih =>
    intro hdg q hq
    simp only [pairsX, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | rfl
    · exact ih (fun t ht => hdg t (by omega)) q hq
    · exact ⟨hS _ (hdg _ (by omega)), hS _ (hdg _ (by omega))⟩

theorem pairsX_length (dg : ℕ → ℕ) (o : ℕ) : ∀ k, (pairsX s dg o k).length = k := by
  intro k; induction k with
  | zero => rfl
  | succ k ih => simp [pairsX, ih]

theorem wordX_left (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 0)) :
    ∀ k, wordX s invAt dg (2 * k) = ((pairsX s dg 0 k).map (fun q => q.1⁻¹ * q.2)).prod := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [wordX, pairsX, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ih, letterX, hinv, Nat.zero_add]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [h1, h2, mul_assoc]

theorem wordX_right (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 1)) :
    ∀ k, wordX s invAt dg (2 * k) = ((pairsX s dg 0 k).map (fun q => q.1 * q.2⁻¹)).prod := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
    rw [e]
    simp only [wordX, pairsX, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one, ih, letterX, hinv, Nat.zero_add]
    have h1 : (2 * k) % 2 = 0 := by omega
    have h2 : (2 * k + 1) % 2 = 1 := by omega
    simp [h1, h2, mul_assoc]

theorem wordX_even (dg : ℕ → ℕ) (hinv : ∀ t, invAt t = decide (t % 2 = 1)) :
    ∀ k, wordX s invAt dg (2 * k + 1) = s (dg 0) * ((pairsX s dg 1 k).map (fun q => q.1⁻¹ * q.2)).prod := by
  intro k
  induction k with
  | zero =>
    simp only [wordX, letterX, hinv, pairsX]
    simp
  | succ k ih =>
    have e : 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 := by ring
    rw [e, wordX_succ, wordX_succ, ih]
    have h1 : letterX s invAt (2 * k + 1) (dg (2 * k + 1)) = (s (dg (2 * k + 1)))⁻¹ := by
      simp only [letterX, hinv]; simp [show (2 * k + 1) % 2 = 1 by omega]
    have h2 : letterX s invAt (2 * k + 1 + 1) (dg (2 * k + 1 + 1)) = s (dg (2 * k + 1 + 1)) := by
      simp only [letterX, hinv]; simp [show (2 * k + 1 + 1) % 2 = 0 by omega]
    rw [h1, h2]
    simp only [pairsX, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]
    rw [show 1 + 2 * k = 2 * k + 1 by ring]
    simp only [mul_assoc]

theorem wordX_map {K' : Type*} [Group K'] (f : K →* K') (dg : ℕ → ℕ) :
    ∀ t, f (wordX s invAt dg t) = wordX (fun u => f (s u)) invAt dg t := by
  intro t
  induction t with
  | zero => exact map_one f
  | succ t ih =>
    rw [wordX_succ, wordX_succ, map_mul, ih]
    congr 1
    unfold letterX
    cases invAt t <;> simp

end Words

theorem wordX_wordG {p n : ℕ} (sG : ℕ → G p n) (invAt : ℕ → Bool) (dg : ℕ → ℕ) :
    ∀ t, wordX sG invAt dg t = wordG sG invAt dg t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih => rw [wordX_succ, wordG_succ, ih]; rfl

/-- Words in a product are pairs of words. -/
theorem wordX_pair {K₁ K₂ : Type*} [Group K₁] [Group K₂] (s₁ : ℕ → K₁) (s₂ : ℕ → K₂) (invAt : ℕ → Bool)
    (dg : ℕ → ℕ) (t : ℕ) :
    wordX (fun u => (s₁ u, s₂ u)) invAt dg t = (wordX s₁ invAt dg t, wordX s₂ invAt dg t) := by
  refine Prod.ext ?_ ?_
  · exact wordX_map (fun u => (s₁ u, s₂ u)) invAt (MonoidHom.fst K₁ K₂) dg t
  · exact wordX_map (fun u => (s₁ u, s₂ u)) invAt (MonoidHom.snd K₁ K₂) dg t

/-! ## Record forms for any group -/

section Record

open BipartiteDD.Haar

theorem gen_record_odd {K : Type*} [Group K] [Fintype K] [DecidableEq K] (sK : ℕ → K) (invL invR : ℕ → Bool)
    (hL : ∀ t, invL t = decide (t % 2 = 0)) (hR : ∀ t, invR t = decide (t % 2 = 1)) (Δ k : ℕ) (hΔ : 0 < Δ)
    (hA : ∀ x : K, ∃ dg : ℕ → ℕ, (∀ t < 2 * k, dg t < Δ) ∧ wordX sK invL dg (2 * k) = x)
    (hB : ∀ x : K, ∃ dg : ℕ → ℕ, (∀ t < 2 * k, dg t < Δ) ∧ wordX sK invR dg (2 * k) = x) :
    ∃ H : SimpleGraph (Fin (2 * Fintype.card K)), BipartiteDD.IsBipartiteDegDiam H Δ (2 * k + 1) := by
  let SS := (Finset.range Δ).image sK
  have hmem : ∀ u < Δ, sK u ∈ SS := fun u hu => Finset.mem_image.2 ⟨u, Finset.mem_range.2 hu, rfl⟩
  have h := record_odd SS ⟨sK 0, hmem 0 hΔ⟩ k
    (fun x => by
      obtain ⟨dg, hdg, hw⟩ := hA x
      refine ⟨pairsX sK dg 0 k, by rw [pairsX_length], pairsX_mem sK hmem dg 0 k (by simpa using hdg), ?_⟩
      rw [← wordX_left sK invL dg hL k, hw])
    (fun x => by
      obtain ⟨dg, hdg, hw⟩ := hB x
      refine ⟨pairsX sK dg 0 k, by rw [pairsX_length], pairsX_mem sK hmem dg 0 k (by simpa using hdg), ?_⟩
      rw [← wordX_right sK invR dg hR k, hw])
  obtain ⟨H, hH⟩ := h
  exact ⟨H, degDiam_mono hH (Finset.card_image_le.trans (Finset.card_range _).le)⟩

theorem gen_record_even {K : Type*} [Group K] [Fintype K] [DecidableEq K] (sK : ℕ → K) (invE : ℕ → Bool)
    (hE : ∀ t, invE t = decide (t % 2 = 1)) (Δ k : ℕ)
    (hA : ∀ x : K, ∃ dg : ℕ → ℕ, (∀ t < 2 * k + 1, dg t < Δ) ∧ wordX sK invE dg (2 * k + 1) = x) :
    ∃ H : SimpleGraph (Fin (2 * Fintype.card K)), BipartiteDD.IsBipartiteDegDiam H Δ (2 * k + 2) := by
  let SS := (Finset.range Δ).image sK
  have hmem : ∀ u < Δ, sK u ∈ SS := fun u hu => Finset.mem_image.2 ⟨u, Finset.mem_range.2 hu, rfl⟩
  have h := record_even SS k
    (fun x => by
      obtain ⟨dg, hdg, hw⟩ := hA x
      refine ⟨sK (dg 0), hmem _ (hdg 0 (by omega)), pairsX sK dg 1 k, by rw [pairsX_length],
        pairsX_mem sK hmem dg 1 k (fun t ht => hdg t (by omega)), ?_⟩
      rw [← hw, wordX_even sK invE dg hE k, inv_mul_cancel_left])
  obtain ⟨H, hH⟩ := h
  exact ⟨H, degDiam_mono hH (Finset.card_image_le.trans (Finset.card_range _).le)⟩

end Record

/-! ## The covers of the first factor, keeping the certificate -/

section Cover

variable {p n : ℕ} (sG : ℕ → G p n) (invAt : ℕ → Bool)

/-- `cover_of_batches`, with an extra condition `E` on the certificates, and the certificate and slot kept. -/
theorem cover_of_batches_ex [Fact p.Prime] [NeZero n] (P : Prm) (hv : P.valid) (hpP : P.p = p) (hnP : P.n = n)
    (hN : P.N = p * n) {ONES RD RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    (hRD : RD = pkF P.w (fun j => j / n) P.N) (hRZ : RZ = pkF P.w (fun j => j % n) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) (hrep : LetRep sG invAt P.Δ P.L lt) (E : ℕ → Prop)
    (hB : ∀ b < P.p * P.p - 1, ∃ Dig, batchOK P ONES lt Dig (kindB P.p b) (aB P.p b * ONES)
      (cond (kindB P.p b) RD 0) (cB P.p b * ONES) (cond (kindB P.p b) 0 RD) RZ = true ∧ E Dig) :
    ∀ x : G p n, ∃ Dig, E Dig ∧ ∃ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      wordG sG invAt (digit (fld P.w Dig j)) P.L = x := by
  intro ⟨A, z⟩
  have h2 := p_two (p := p)
  have hw : 2 ≤ P.w := by have := hv.1; omega
  have hpw : p < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hpP]; nlinarith
  have hnw : n < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hnP]; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hzv := ZMod.val_lt (Multiplicative.toAdd z)
  have hdet := det_entries A
  by_cases hc : A 1 0 = 0
  · have ha1 := val_pos_of_ne (a_ne_of_c A hc)
    have hav := ZMod.val_lt (A 0 0)
    have hbv := ZMod.val_lt (A 0 1)
    obtain ⟨hbk, haB, hcB, hbl⟩ := bat_nc h2 ha1 hav
    obtain ⟨Dig, hDig, hE⟩ := hB (p * (p - 1) + ((A 0 0).val - 1)) (by rw [hpP]; exact hbl)
    rw [hpP, hbk] at hDig
    simp only [cond_true] at hDig
    rw [haB, hcB, zero_mul] at hDig
    obtain ⟨j, hj⟩ : ∃ j, j = (A 0 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
    have hjN : j < P.N := by
      rw [hN]
      calc j < (A 0 1).val * n + n := by omega
        _ = ((A 0 1).val + 1) * n := by ring
        _ ≤ p * n := Nat.mul_le_mul_right _ hbv
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun j => j / n) (tc := fun _ => 0)
      (td := fun _ => 0) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) hRD h0 h0 hRZ
      (fun j hj' => ⟨by omega, by
        have : j / n < p := (Nat.div_lt_iff_lt_mul hn0).2 (by rw [← hN]; exact hj')
        omega, by positivity, by positivity, by
        have := Nat.mod_lt j hn0; omega⟩) hDig j hjN
    obtain ⟨hdg, ma, mc, mz, mb, -⟩ := this
    refine ⟨Dig, hE, j, hjN, hdg, ?_⟩
    obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc mb
    rw [hnP] at mz
    have hja : j / n = (A 0 1).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
    have hjz : j % n = (Multiplicative.toAdd z).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
    have Wz : (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = z := by
      apply Multiplicative.toAdd.injective
      rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
    refine Prod.ext (eq_of_entries_nc hc ?_ ?_ ?_) Wz
    · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    · rw [← eb, cast_of_modEq (mb rfl), hja, ZMod.natCast_zmod_val]
    · rw [← ec, cast_of_modEq mc, Nat.cast_zero]
  · have hav := ZMod.val_lt (A 0 0)
    have hcv := ZMod.val_lt (A 1 0)
    have hdv := ZMod.val_lt (A 1 1)
    have hc1 := val_pos_of_ne hc
    obtain ⟨hbk, haB, hcB, hbl⟩ := bat_c h2 hav hc1 hcv
    obtain ⟨Dig, hDig, hE⟩ := hB ((A 0 0).val * (p - 1) + ((A 1 0).val - 1)) (by rw [hpP]; exact hbl)
    rw [hpP, hbk] at hDig
    simp only [cond_false] at hDig
    rw [haB, hcB] at hDig
    obtain ⟨j, hj⟩ : ∃ j, j = (A 1 1).val * n + (Multiplicative.toAdd z).val := ⟨_, rfl⟩
    have hjN : j < P.N := by
      rw [hN]
      calc j < (A 1 1).val * n + n := by omega
        _ = ((A 1 1).val + 1) * n := by ring
        _ ≤ p * n := Nat.mul_le_mul_right _ hdv
    have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun _ => 0) (tc := fun _ => (A 1 0).val)
      (td := fun j => j / n) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) h0 (by rw [hO, ← pkF_const])
      hRD hRZ
      (fun j hj' => ⟨by omega, by positivity, by omega, by
        have : j / n < p := (Nat.div_lt_iff_lt_mul hn0).2 (by rw [← hN]; exact hj')
        omega, by
        have := Nat.mod_lt j hn0; omega⟩) hDig j hjN
    obtain ⟨hdg, ma, mc, mz, -, md⟩ := this
    refine ⟨Dig, hE, j, hjN, hdg, ?_⟩
    obtain ⟨ea, eb, ec, ed, ez⟩ := semN_rep (p := p) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc md
    rw [hnP] at mz
    have hjd : j / n = (A 1 1).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_div_right _ _ hn0, Nat.div_eq_of_lt hzv, Nat.zero_add]
    have hjz : j % n = (Multiplicative.toAdd z).val := by
      rw [hj, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hzv]
    have Wz : (wordG sG invAt (digit (fld P.w Dig j)) P.L).2 = z := by
      apply Multiplicative.toAdd.injective
      rw [← ez, cast_of_modEq mz, hjz, ZMod.natCast_zmod_val]
    refine Prod.ext (eq_of_entries_c hc ?_ ?_ ?_) Wz
    · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    · rw [← ec, cast_of_modEq mc, ZMod.natCast_zmod_val]
    · rw [← ed, cast_of_modEq (md rfl), hjd, ZMod.natCast_zmod_val]

/-- `cover_of_batches_pm`, with an extra condition `E` on the certificates, and the certificate and slot kept. -/
theorem cover_of_batches_pm_ex [hp : Fact p.Prime] [NeZero n] (hp2 : p ≠ 2) (P : Prm) (hv : P.valid)
    (hpP : P.p = p) (hnP : P.n = n) (hN : P.N = p * n) {ONES RD NRD RZ : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (hRD : RD = pkF P.w (fun j => j / P.n) P.N)
    (hNRD : NRD = pkF P.w (fun j => (P.p - j / P.n) % P.p) P.N) (hRZ : RZ = pkF P.w (fun j => j % P.n) P.N)
    {lt : ℕ → ℕ → Let} (hlt : LetOK P lt) (hrep : LetRep sG invAt P.Δ P.L lt) (E : ℕ → Prop)
    (hB : ∀ b < P.p * hP P.p + hP P.p, ∃ Dig,
      batchOKpm P ONES lt Dig (kindBp P.p b) (aBp P.p b) (cBp P.p b) RD NRD RZ = true ∧ E Dig) :
    ∀ x : G p n, ∃ Dig, E Dig ∧ ∃ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (wordG sG invAt (digit (fld P.w Dig j)) P.L = x ∨ wordG sG invAt (digit (fld P.w Dig j)) P.L = gneg * x) := by
  have h2 := p_two (p := p)
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have hh : 2 * hP p + 1 = p := by unfold hP; omega
  have hh1 : 1 ≤ hP p := by unfold hP; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hNp : P.N = P.p * P.n := by rw [hN, hpP, hnP]
  have core : ∀ x : G p n, ((x.1 1 0 ≠ 0 ∧ (x.1 1 0).val ≤ hP p) ∨ (x.1 1 0 = 0 ∧ (x.1 0 0).val ≤ hP p)) →
      ∃ Dig, E Dig ∧ ∃ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
        (wordG sG invAt (digit (fld P.w Dig j)) P.L = x ∨
          wordG sG invAt (digit (fld P.w Dig j)) P.L = gneg * x) := by
    intro ⟨A, z⟩ hcan
    have hzv := ZMod.val_lt (Multiplicative.toAdd z)
    have hav := ZMod.val_lt (A 0 0)
    have hbv := ZMod.val_lt (A 0 1)
    have hcv := ZMod.val_lt (A 1 0)
    have hdv := ZMod.val_lt (A 1 1)
    rcases hcan with ⟨hc, hch⟩ | ⟨hc, hah⟩
    · have hc1 := val_pos_of_ne hc
      obtain ⟨hbk, haB, hcB, hbl⟩ := batp_c hh1 hav hc1 hch
      obtain ⟨Dig, hDig, hE⟩ := hB ((A 0 0).val * hP p + ((A 1 0).val - 1)) (by rw [hpP]; exact hbl)
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
      refine ⟨Dig, hE, j, hjN, hdg, ?_⟩
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
    · have ha1 := val_pos_of_ne (a_ne_of_c A hc)
      obtain ⟨hbk, haB, hbl⟩ := batp_nc hh1 ha1 hah
      obtain ⟨Dig, hDig, hE⟩ := hB (p * hP p + ((A 0 0).val - 1)) (by rw [hpP]; exact hbl)
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
      refine ⟨Dig, hE, j, hjN, hdg, ?_⟩
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
    obtain ⟨Dig, hE, j, hjN, hdg, hw⟩ := core _ hcan'
    refine ⟨Dig, hE, j, hjN, hdg, ?_⟩
    rcases hw with hw | hw
    · exact Or.inr hw
    · exact Or.inl (hw.trans (gneg_gneg x))

end Cover

/-! ## The second factor: constant targets -/

section Second

variable {q n : ℕ}

/-- The batch of a matrix of `SL(2, q)` (as in `cover_of_batches`). -/
noncomputable def bS (A : SpecialLinearGroup (Fin 2) (ZMod q)) : ℕ :=
  if A 1 0 = 0 then q * (q - 1) + ((A 0 0).val - 1) else (A 0 0).val * (q - 1) + ((A 1 0).val - 1)

/-- The free entry of a matrix in its batch: `b` if `c = 0`, else `d`. -/
noncomputable def jS (A : SpecialLinearGroup (Fin 2) (ZMod q)) : ℕ :=
  if A 1 0 = 0 then (A 0 1).val else (A 1 1).val

theorem bS_lt [Fact q.Prime] (A : SpecialLinearGroup (Fin 2) (ZMod q)) : bS A < q * q - 1 := by
  have h2 := p_two (p := q)
  unfold bS
  split_ifs with hc
  · exact (bat_nc h2 (val_pos_of_ne (a_ne_of_c A hc)) (ZMod.val_lt _)).2.2.2
  · exact (bat_c h2 (ZMod.val_lt _) (val_pos_of_ne hc) (ZMod.val_lt _)).2.2.2

theorem jS_lt [NeZero q] (A : SpecialLinearGroup (Fin 2) (ZMod q)) : jS A < q := by
  unfold jS; split_ifs <;> exact ZMod.val_lt _

/-- A word that meets the constant targets of `A`'s batch at some slot has matrix `A`. -/
theorem word_const [Fact q.Prime] [NeZero n] (sG : ℕ → G q n) (invAt : ℕ → Bool) (P : Prm) (hv : P.valid)
    (hpP : P.p = q) (hnP : P.n = n) {ONES RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N)
    (hRZ : RZ = pkF P.w (fun j => j % n) P.N) {lt : ℕ → ℕ → Let} (hlt : LetOK P lt)
    (hrep : LetRep sG invAt P.Δ P.L lt) (A : SpecialLinearGroup (Fin 2) (ZMod q)) {Dig : ℕ}
    (h : batchOK P ONES lt Dig (kindB q (bS A)) (aB q (bS A) * ONES) (cond (kindB q (bS A)) (jS A * ONES) 0)
      (cB q (bS A) * ONES) (cond (kindB q (bS A)) 0 (jS A * ONES)) RZ = true)
    {j : ℕ} (hj : j < P.N) : (wordG sG invAt (digit (fld P.w Dig j)) P.L).1 = A := by
  have h2 := p_two (p := q)
  have hw : 2 ≤ P.w := by have := hv.1; omega
  have hpw : q < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hpP]; nlinarith
  have hnw : n < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hnP]; omega
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hav := ZMod.val_lt (A 0 0)
  have hbv := ZMod.val_lt (A 0 1)
  have hcv := ZMod.val_lt (A 1 0)
  have hdv := ZMod.val_lt (A 1 1)
  have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
  by_cases hc : A 1 0 = 0
  · have ha1 := val_pos_of_ne (a_ne_of_c A hc)
    obtain ⟨hbk, haB, hcB, -⟩ := bat_nc h2 ha1 hav
    have eb : bS A = q * (q - 1) + ((A 0 0).val - 1) := by unfold bS; rw [if_pos hc]
    have ej : jS A = (A 0 1).val := by unfold jS; rw [if_pos hc]
    rw [eb, ej, hbk, haB, hcB, zero_mul] at h
    simp only [cond_true] at h
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun _ => (A 0 1).val) (tc := fun _ => 0)
      (td := fun _ => 0) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) (by rw [hO, ← pkF_const]) h0 h0 hRZ
      (fun j _ => ⟨by omega, by omega, by positivity, by positivity, by
        have := Nat.mod_lt j hn0; omega⟩) h j hj
    obtain ⟨hdg, ma, mc, -, mb, -⟩ := this
    obtain ⟨ea, eb', ec, -, -⟩ := semN_rep (p := q) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc mb
    refine eq_of_entries_nc hc ?_ ?_ ?_
    · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    · rw [← eb', cast_of_modEq (mb rfl), ZMod.natCast_zmod_val]
    · rw [← ec, cast_of_modEq mc, Nat.cast_zero]
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_c h2 hav (val_pos_of_ne hc) hcv
    have eb : bS A = (A 0 0).val * (q - 1) + ((A 1 0).val - 1) := by unfold bS; rw [if_neg hc]
    have ej : jS A = (A 1 1).val := by unfold jS; rw [if_neg hc]
    rw [eb, ej, hbk, haB, hcB] at h
    simp only [cond_false] at h
    have := batch_sound P hv hO hlt (ta := fun _ => (A 0 0).val) (tb := fun _ => 0) (tc := fun _ => (A 1 0).val)
      (td := fun _ => (A 1 1).val) (tz := fun j => j % n) (by rw [hO, ← pkF_const]) h0 (by rw [hO, ← pkF_const])
      (by rw [hO, ← pkF_const]) hRZ
      (fun j _ => ⟨by omega, by positivity, by omega, by omega, by
        have := Nat.mod_lt j hn0; omega⟩) h j hj
    obtain ⟨hdg, ma, mc, -, -, md⟩ := this
    obtain ⟨ea, -, ec, ed, -⟩ := semN_rep (p := q) (n := n) sG invAt hrep _ P.L (le_refl _) hdg
    rw [hpP] at ma mc md
    refine eq_of_entries_c hc ?_ ?_ ?_
    · rw [← ea, cast_of_modEq ma, ZMod.natCast_zmod_val]
    · rw [← ec, cast_of_modEq mc, ZMod.natCast_zmod_val]
    · rw [← ed, cast_of_modEq (md rfl), ZMod.natCast_zmod_val]

end Second

/-! ## The product covers -/

section Prod

variable {p q n : ℕ}

theorem flat_index {B Q b2 j2 b : ℕ} (hB : 0 < B) (hQ : 0 < Q) (hb2 : b2 < Q * Q - 1) (hj2 : j2 < Q) (hb : b < B) :
    ((b2 * Q + j2) * B + b) % B = b ∧ ((b2 * Q + j2) * B + b) / B / Q = b2 ∧
      ((b2 * Q + j2) * B + b) / B % Q = j2 ∧ (b2 * Q + j2) * B + b < (Q * Q - 1) * Q * B := by
  have e1 : ((b2 * Q + j2) * B + b) / B = b2 * Q + j2 := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt hb, Nat.zero_add]
  refine ⟨by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb], ?_, ?_, ?_⟩
  · rw [e1, Nat.add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hj2, Nat.zero_add]
  · rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj2]
  · have h1 : b2 * Q + j2 + 1 ≤ (Q * Q - 1) * Q := by
      have : (b2 + 1) * Q ≤ (Q * Q - 1) * Q := Nat.mul_le_mul_right _ (by omega)
      nlinarith
    calc (b2 * Q + j2) * B + b < (b2 * Q + j2) * B + B := by omega
      _ = (b2 * Q + j2 + 1) * B := by ring
      _ ≤ (Q * Q - 1) * Q * B := Nat.mul_le_mul_right _ h1

/-- **The cover of `SL(2,p) × Z_n × SL(2,q)`.** Batch `i` checks the first factor's batch `i % (p² - 1)` and
the constant targets of the second factor's batch `i / (p² - 1) / q`, slot value `i / (p² - 1) % q`. -/
theorem cover_prod [Fact p.Prime] [Fact q.Prime] [NeZero n] (sG₁ : ℕ → G p n) (sG₂ : ℕ → G q n)
    (invAt : ℕ → Bool) (P₁ P₂ : Prm) (hv₁ : P₁.valid) (hv₂ : P₂.valid) (hpP : P₁.p = p) (hnP : P₁.n = n)
    (hN : P₁.N = p * n) (hqP : P₂.p = q) (hnP₂ : P₂.n = n) (hN₂ : P₂.N = P₁.N) (hw₂ : P₂.w = P₁.w)
    (hΔ₂ : P₂.Δ = P₁.Δ) (hL₂ : P₂.L = P₁.L) {ONES RD RZ : ℕ} (hO : ONES = pkF P₁.w (fun _ => 1) P₁.N)
    (hRD : RD = pkF P₁.w (fun j => j / n) P₁.N) (hRZ : RZ = pkF P₁.w (fun j => j % n) P₁.N)
    {lt₁ lt₂ : ℕ → ℕ → Let} (hlt₁ : LetOK P₁ lt₁) (hlt₂ : LetOK P₂ lt₂)
    (hrep₁ : LetRep sG₁ invAt P₁.Δ P₁.L lt₁) (hrep₂ : LetRep sG₂ invAt P₂.Δ P₂.L lt₂)
    (hB : ∀ i < (q * q - 1) * q * (p * p - 1), ∃ Dig,
      batchOK P₁ ONES lt₁ Dig (kindB p (i % (p * p - 1))) (aB p (i % (p * p - 1)) * ONES)
        (cond (kindB p (i % (p * p - 1))) RD 0) (cB p (i % (p * p - 1)) * ONES)
        (cond (kindB p (i % (p * p - 1))) 0 RD) RZ = true ∧
      batchOK P₂ ONES lt₂ Dig (kindB q (i / (p * p - 1) / q)) (aB q (i / (p * p - 1) / q) * ONES)
        (cond (kindB q (i / (p * p - 1) / q)) (i / (p * p - 1) % q * ONES) 0) (cB q (i / (p * p - 1) / q) * ONES)
        (cond (kindB q (i / (p * p - 1) / q)) 0 (i / (p * p - 1) % q * ONES)) RZ = true) :
    ∀ x : G p n × SpecialLinearGroup (Fin 2) (ZMod q), ∃ dg : ℕ → ℕ, (∀ t < P₁.L, dg t < P₁.Δ) ∧
      wordX (fun u => (sG₁ u, (sG₂ u).1)) invAt dg P₁.L = x := by
  intro ⟨x₁, A₂⟩
  have h2p := p_two (p := p)
  have h2q := p_two (p := q)
  have hB0 : 0 < p * p - 1 := by
    have : 4 ≤ p * p := by nlinarith
    omega
  have hcov := cover_of_batches_ex sG₁ invAt P₁ hv₁ hpP hnP hN hO hRD hRZ hlt₁ hrep₁
    (fun Dig => batchOK P₂ ONES lt₂ Dig (kindB q (bS A₂)) (aB q (bS A₂) * ONES)
      (cond (kindB q (bS A₂)) (jS A₂ * ONES) 0) (cB q (bS A₂) * ONES) (cond (kindB q (bS A₂)) 0 (jS A₂ * ONES))
      RZ = true)
    (fun b hb => by
      rw [hpP] at hb ⊢
      obtain ⟨e1, e2, e3, e4⟩ := flat_index hB0 (by omega) (bS_lt A₂) (jS_lt A₂) hb
      have := hB _ e4
      rw [e1, e2, e3] at this
      exact this)
  obtain ⟨Dig, hE, j, hjN, hdg, hw⟩ := hcov x₁
  refine ⟨digit (fld P₁.w Dig j), hdg, ?_⟩
  rw [wordX_pair, wordX_wordG]
  refine Prod.ext hw ?_
  have h2 : (wordX (fun u => (sG₂ u).1) invAt (digit (fld P₁.w Dig j)) P₁.L) =
      (wordG sG₂ invAt (digit (fld P₁.w Dig j)) P₁.L).1 := by
    rw [← wordX_wordG]
    exact (wordX_map sG₂ invAt (MonoidHom.fst _ _) _ _).symm
  rw [h2]
  have := word_const sG₂ invAt P₂ hv₂ hqP hnP₂ (by rw [hO, hw₂, hN₂]) (by rw [hRZ, hw₂, hN₂]) hlt₂ hrep₂ A₂ hE
    (j := j) (by rw [hN₂]; exact hjN)
  rw [hw₂, hL₂] at this
  exact this

/-- **The cover of `PSL(2,p) × Z_n × SL(2,q)`.** As `cover_prod`, with sign-normalised batches in the first
factor (`(p² - 1) / 2` of them). -/
theorem cover_prod_pm [Fact p.Prime] [Fact q.Prime] [NeZero n] (hp2 : p ≠ 2) (sG₁ : ℕ → G p n)
    (sG₂ : ℕ → G q n) (invAt : ℕ → Bool) (P₁ P₂ : Prm) (hv₁ : P₁.valid) (hv₂ : P₂.valid) (hpP : P₁.p = p)
    (hnP : P₁.n = n) (hN : P₁.N = p * n) (hqP : P₂.p = q) (hnP₂ : P₂.n = n) (hN₂ : P₂.N = P₁.N)
    (hw₂ : P₂.w = P₁.w) (hΔ₂ : P₂.Δ = P₁.Δ) (hL₂ : P₂.L = P₁.L) {ONES RD NRD RZ : ℕ}
    (hO : ONES = pkF P₁.w (fun _ => 1) P₁.N) (hRD : RD = pkF P₁.w (fun j => j / P₁.n) P₁.N)
    (hNRD : NRD = pkF P₁.w (fun j => (P₁.p - j / P₁.n) % P₁.p) P₁.N) (hRZ : RZ = pkF P₁.w (fun j => j % P₁.n) P₁.N)
    {lt₁ lt₂ : ℕ → ℕ → Let} (hlt₁ : LetOK P₁ lt₁) (hlt₂ : LetOK P₂ lt₂)
    (hrep₁ : LetRep sG₁ invAt P₁.Δ P₁.L lt₁) (hrep₂ : LetRep sG₂ invAt P₂.Δ P₂.L lt₂)
    (hB : ∀ i < (q * q - 1) * q * (p * hP p + hP p), ∃ Dig,
      batchOKpm P₁ ONES lt₁ Dig (kindBp p (i % (p * hP p + hP p))) (aBp p (i % (p * hP p + hP p)))
        (cBp p (i % (p * hP p + hP p))) RD NRD RZ = true ∧
      batchOK P₂ ONES lt₂ Dig (kindB q (i / (p * hP p + hP p) / q)) (aB q (i / (p * hP p + hP p) / q) * ONES)
        (cond (kindB q (i / (p * hP p + hP p) / q)) (i / (p * hP p + hP p) % q * ONES) 0)
        (cB q (i / (p * hP p + hP p) / q) * ONES)
        (cond (kindB q (i / (p * hP p + hP p) / q)) 0 (i / (p * hP p + hP p) % q * ONES)) RZ = true) :
    ∀ x : PG p n × SpecialLinearGroup (Fin 2) (ZMod q), ∃ dg : ℕ → ℕ, (∀ t < P₁.L, dg t < P₁.Δ) ∧
      wordX (fun u => (pi (sG₁ u), (sG₂ u).1)) invAt dg P₁.L = x := by
  intro ⟨y₁, A₂⟩
  obtain ⟨x₁, rfl⟩ := pi_surj y₁
  have h2p := p_two (p := p)
  have h2q := p_two (p := q)
  have hB0 : 0 < p * hP p + hP p := by
    have : 1 ≤ hP p := by
      unfold hP
      rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
      · exact absurd h hp2
      · omega
    nlinarith
  have hcov := cover_of_batches_pm_ex sG₁ invAt hp2 P₁ hv₁ hpP hnP hN hO hRD hNRD hRZ hlt₁ hrep₁
    (fun Dig => batchOK P₂ ONES lt₂ Dig (kindB q (bS A₂)) (aB q (bS A₂) * ONES)
      (cond (kindB q (bS A₂)) (jS A₂ * ONES) 0) (cB q (bS A₂) * ONES) (cond (kindB q (bS A₂)) 0 (jS A₂ * ONES))
      RZ = true)
    (fun b hb => by
      rw [hpP] at hb ⊢
      obtain ⟨e1, e2, e3, e4⟩ := flat_index hB0 (by omega) (bS_lt A₂) (jS_lt A₂) hb
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
  · show wordX (fun u => (sG₂ u).1) invAt (digit (fld P₁.w Dig j)) P₁.L = A₂
    have h2 : (wordX (fun u => (sG₂ u).1) invAt (digit (fld P₁.w Dig j)) P₁.L) =
        (wordG sG₂ invAt (digit (fld P₁.w Dig j)) P₁.L).1 := by
      rw [← wordX_wordG]
      exact (wordX_map sG₂ invAt (MonoidHom.fst _ _) _ _).symm
    rw [h2]
    have := word_const sG₂ invAt P₂ hv₂ hqP hnP₂ (by rw [hO, hw₂, hN₂]) (by rw [hRZ, hw₂, hN₂, hnP]) hlt₂ hrep₂
      A₂ hE (j := j) (by rw [hN₂]; exact hjN)
    rw [hw₂, hL₂] at this
    exact this

/-- The order of `PSL(2,p) × Z_n × SL(2,q)`, doubled. -/
theorem card_PG_SL [Fact p.Prime] [Fact q.Prime] [NeZero n] (hp2 : p ≠ 2) :
    Nat.card (PG p n × SpecialLinearGroup (Fin 2) (ZMod q)) * 2 = p * (p * p - 1) * n * (q * (q * q - 1)) := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := SpecialLinearGroup (Fin 2) (ZMod q)), card_SL,
    ← card_PG (p := p) (n := n) hp2]
  ring

end Prod

end BipartiteDD.LeanAll.HaarProd2
