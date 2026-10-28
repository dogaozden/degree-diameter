import BipartiteDD.LeanAll.GF8
import BipartiteDD.LeanAll.HaarProd

/-! # Packed checks over `GF(8)`, and Haar graphs of `PSL(2,p) × Z_n × SL(2,8)`

The second factor's letters are matrices over `GF8`; a packed state holds the spaced codes (`GF8.sp`) of the four
entries of every slot. A step multiplies by the slot's letter: selection of the letter's spaced entries as in
`HaarSwar`, integer products (no carries between the spaced bits), then `red8`, the fieldwise `GF8.red1`
(`red8_eq`, `GF8.red1_sp`). `batch_sound8` reads the final states against constant targets; `word_const8` turns that
into equality in `SL(2, GF8)`, and `cover_prod8` is `HaarProd.cover_prod_pm` with this second factor. -/

namespace BipartiteDD.LeanAll.HaarGF8

open BipartiteDD.LeanAll BipartiteDD.LeanAll.GF8 BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.Swar
open BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.HaarPSL BipartiteDD.LeanAll.HaarProd Matrix

/-- Matrix entries `(a, b, c, d)` over `GF8`. -/
abbrev Q8 := GF8 × GF8 × GF8 × GF8

/-- A letter with spaced entries (no shift). -/
def spL (q : Q8) : Let := ⟨sp q.1, sp q.2.1, sp q.2.2.1, sp q.2.2.2, 0⟩

/-- The product of entry quadruples. -/
def mulQ (x l : Q8) : Q8 :=
  (x.1 * l.1 + x.2.1 * l.2.2.1, x.1 * l.2.1 + x.2.1 * l.2.2.2, x.2.2.1 * l.1 + x.2.2.2 * l.2.2.1,
    x.2.2.1 * l.2.1 + x.2.2.2 * l.2.2.2)

/-- What a slot with digits `dg` computes in `t` letters. -/
def semG (lm : ℕ → ℕ → Q8) (dg : ℕ → ℕ) : ℕ → Q8
  | 0 => (1, 0, 0, 1)
  | t + 1 => mulQ (semG lm dg t) (lm t (dg t))

section Comp

variable (P : Prm) (ONES : ℕ) (lm : ℕ → ℕ → Q8)

/-- Fieldwise `red1`. -/
def red8 (V : ℕ) : ℕ :=
  ((V &&& (73 * ONES)) + ((V >>> 9) &&& ONES) * 9 + ((V >>> 12) &&& ONES) * 72) &&& (73 * ONES)

/-- One step over `GF8`. -/
def stepG (Dig t : ℕ) (X : St) : St × Bool :=
  let Dt := (Dig >>> (4 * t)) &&& (15 * ONES)
  let A := red8 ONES (selSum P ONES Dt (fun u => X.a * (spL (lm t u)).e + X.b * (spL (lm t u)).g) P.Δ)
  let Bq := red8 ONES (selSum P ONES Dt (fun u => X.a * (spL (lm t u)).f + X.b * (spL (lm t u)).h) P.Δ)
  let C := red8 ONES (selSum P ONES Dt (fun u => X.c * (spL (lm t u)).e + X.d * (spL (lm t u)).g) P.Δ)
  let D := red8 ONES (selSum P ONES Dt (fun u => X.c * (spL (lm t u)).f + X.d * (spL (lm t u)).h) P.Δ)
  (⟨A, Bq, C, D, 0⟩, Nat.beq (thr ONES Dt P.Δ) 0)

/-- The first `t` steps. -/
def runG (Dig t : ℕ) : St × Bool :=
  Nat.rec (motive := fun _ => St × Bool) (⟨ONES, 0, 0, ONES, 0⟩, true)
    (fun t acc => let r := stepG P ONES lm Dig t acc.1; (r.1, acc.2 && r.2)) t

/-- The batch check over `GF8`: the certificate fits, the digits are letters, and the final entries are the targets
(`a`, `c` and, by `kind`, `b` or `d`). -/
def batchOK8 (Dig : ℕ) (kind : Bool) (TA TB TC TD : ℕ) : Bool :=
  Nat.blt Dig (2 ^ (P.w * P.N)) &&
    ((runG P ONES lm Dig P.L).2 && Nat.beq (runG P ONES lm Dig P.L).1.a TA &&
      Nat.beq (runG P ONES lm Dig P.L).1.c TC &&
      cond kind (Nat.beq (runG P ONES lm Dig P.L).1.b TB) (Nat.beq (runG P ONES lm Dig P.L).1.d TD))

end Comp

/-- `X` packs the spaced codes of the slot states `xs`. -/
def Rep8 (P : Prm) (X : St) (xs : ℕ → Q8) : Prop :=
  X.a = pkF P.w (fun j => sp (xs j).1) P.N ∧ X.b = pkF P.w (fun j => sp (xs j).2.1) P.N ∧
  X.c = pkF P.w (fun j => sp (xs j).2.2.1) P.N ∧ X.d = pkF P.w (fun j => sp (xs j).2.2.2) P.N

theorem red8_eq {w N : ℕ} (hw : 16 ≤ w) {ONES V : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF w v N) (hv : ∀ j < N, v j < 2 ^ 15) : red8 ONES V = pkF w (fun j => red1 (v j)) N := by
  have hw0 : 0 < w := by omega
  have h15 : (2 : ℕ) ^ 15 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvw : ∀ j < N, v j < 2 ^ w := fun j hj => lt_of_lt_of_le (hv j hj) h15
  have c73 : (73 : ℕ) < 2 ^ w := lt_of_lt_of_le (by norm_num) h15
  have e1 : V &&& (73 * ONES) = pkF w (fun j => v j &&& 73) N := by
    rw [hV, hO, ← pkF_const, pkF_land hw0 hvw (fun _ _ => c73)]
  have e2 : (V >>> 9) &&& ONES = pkF w (fun j => (v j >>> 9) &&& 1) N := by
    rw [hV, hO, pkF_shr_land hw0 (by omega) (Nat.one_lt_two_pow (by omega)) hvw]
  have e3 : (V >>> 12) &&& ONES = pkF w (fun j => (v j >>> 12) &&& 1) N := by
    rw [hV, hO, pkF_shr_land hw0 (by omega) (Nat.one_lt_two_pow (by omega)) hvw]
  have hs : ∀ j < N, (v j &&& 73) + ((v j >>> 9) &&& 1) * 9 + ((v j >>> 12) &&& 1) * 72 < 2 ^ w := by
    intro j _
    have a1 : v j &&& 73 ≤ 73 := Nat.and_le_right
    have a2 : (v j >>> 9) &&& 1 ≤ 1 := Nat.and_le_right
    have a3 : (v j >>> 12) &&& 1 ≤ 1 := Nat.and_le_right
    have : (v j &&& 73) + ((v j >>> 9) &&& 1) * 9 + ((v j >>> 12) &&& 1) * 72 ≤ 154 := by omega
    exact lt_of_le_of_lt this (lt_of_lt_of_le (by norm_num) h15)
  unfold red8
  rw [e1, e2, e3, mul_comm _ 9, mul_comm _ 72, ← pkF_mul, ← pkF_mul, ← pkF_add, ← pkF_add, hO, ← pkF_const,
    pkF_land hw0 (fun j hj => by have := hs j hj; simpa [mul_comm] using this) (fun _ _ => c73)]
  exact pkF_congr (fun j _ => by unfold red1; ring_nf)

theorem lin_eq8 {w N : ℕ} {X Y : ℕ} {x y : ℕ → GF8} (hX : X = pkF w (fun j => sp (x j)) N)
    (hY : Y = pkF w (fun j => sp (y j)) N) (e g : GF8) :
    X * sp e + Y * sp g = pkF w (fun j => sp (x j) * sp e + sp (y j) * sp g) N :=
  lin_eq hX hY (sp e) (sp g)

theorem step_sound8 (P : Prm) (hw16 : 16 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q8) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) {t : ℕ} (ht : t < P.L) {X : St} {xs : ℕ → Q8}
    (hX : Rep8 P X xs) (hok : (stepG P ONES lm Dig t X).2 = true) :
    Rep8 P (stepG P ONES lm Dig t X).1 (fun j => mulQ (xs j) (lm t (digit (F j) t))) ∧
      ∀ j < P.N, digit (F j) t < P.Δ := by
  obtain ⟨hXa, hXb, hXc, hXd⟩ := hX
  have hw8 : 8 ≤ P.w := by omega
  have hw : 0 < P.w := by omega
  have hD := dig_eq hw hO hDig hF (t := t) (by omega)
  have hdt : ∀ j < P.N, (fun j => (F j >>> (4 * t)) &&& 15) j < 16 := fun j _ => digit_lt (F j) t
  simp only [stepG, Nat.beq_eq] at hok
  have hdΔ : ∀ j < P.N, digit (F j) t < P.Δ := by
    rw [thr_eq hw8 hO hD hdt hΔ] at hok
    have h0' : pkF P.w (fun j => if P.Δ ≤ (F j >>> (4 * t)) &&& 15 then 1 else 0) P.N =
        pkF P.w (fun _ => 0) P.N := by rw [hok, pkF_const]; simp
    have := pkF_inj hw (fun j _ => by split_ifs <;> simp [Nat.one_lt_two_pow_iff] <;> omega)
      (fun _ _ => by positivity) h0'
    intro j hj
    have h1 := this j hj
    unfold digit
    split_ifs at h1 with h2
    all_goals first | omega | simp at h1
  have h15 : (2 : ℕ) ^ 15 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have entry : ∀ (Xu Xv : ℕ) (xu xv : ℕ → GF8), Xu = pkF P.w (fun j => sp (xu j)) P.N →
      Xv = pkF P.w (fun j => sp (xv j)) P.N → (E G : ℕ → GF8) →
      red8 ONES (selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ) =
        pkF P.w (fun j => sp (xu j * E (digit (F j) t) + xv j * G (digit (F j) t))) P.N := by
    intro Xu Xv xu xv hu hvv E G
    have hsel := selSum_eq P hw8 hO hD hdt (fun u => lin_eq8 hu hvv (E u) (G u)) hΔ
      (fun u _ j _ => lt_of_lt_of_le (lin_lt _ _ _ _) h15) P.Δ (le_refl _)
    have hsel' : selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ =
        pkF P.w (fun j => sp (xu j) * sp (E (digit (F j) t)) + sp (xv j) * sp (G (digit (F j) t))) P.N := by
      rw [hsel]
      exact pkF_congr (fun j hj => by simp only [digit] at hdΔ ⊢; simp [hdΔ j hj])
    rw [red8_eq hw16 hO hsel' (fun j _ => lin_lt _ _ _ _)]
    exact pkF_congr (fun j _ => red1_sp _ _ _ _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hdΔ⟩
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)

theorem run_sound8 (P : Prm) (hw16 : 16 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q8) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) :
    ∀ t ≤ P.L, (runG P ONES lm Dig t).2 = true →
      Rep8 P (runG P ONES lm Dig t).1 (fun j => semG lm (digit (F j)) t) ∧
        ∀ j < P.N, ∀ t' < t, digit (F j) t' < P.Δ := by
  intro t
  induction t with
  | zero =>
    intro _ _
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun j _ t' h => absurd h (by omega)⟩
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG, sp_one])
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG, sp_zero]), pkF_const, zero_mul]
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG, sp_zero]), pkF_const, zero_mul]
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG, sp_one])
  | succ t ih =>
    intro ht hok
    have e : runG P ONES lm Dig (t + 1) =
        ((stepG P ONES lm Dig t (runG P ONES lm Dig t).1).1,
          (runG P ONES lm Dig t).2 && (stepG P ONES lm Dig t (runG P ONES lm Dig t).1).2) := rfl
    rw [e] at hok ⊢
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hX, hxs⟩ := ih (by omega) hok.1
    obtain ⟨hY, hys⟩ := step_sound8 P hw16 hwL hΔ hO lm hDig hF (by omega) hX hok.2
    refine ⟨hY, fun j hj t' h => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact hxs j hj t' h
    · subst h; exact hys j hj

/-- **Soundness of a `GF8` batch with constant targets.** -/
theorem batch_sound8 (P : Prm) (hw16 : 16 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q8) {Dig : ℕ} {kind : Bool} {a b c d : GF8}
    (h : batchOK8 P ONES lm Dig kind (sp a * ONES) (sp b * ONES) (sp c * ONES) (sp d * ONES) = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semG lm (digit (fld P.w Dig j)) P.L).1 = a ∧ (semG lm (digit (fld P.w Dig j)) P.L).2.2.1 = c ∧
      (kind = true → (semG lm (digit (fld P.w Dig j)) P.L).2.1 = b) ∧
      (kind = false → (semG lm (digit (fld P.w Dig j)) P.L).2.2.2 = d) := by
  have hw : 0 < P.w := by omega
  have h15 : (2 : ℕ) ^ 15 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have spw : ∀ x : GF8, sp x < 2 ^ P.w := fun x => lt_of_lt_of_le (lt_trans (sp_lt x) (by norm_num)) h15
  unfold batchOK8 at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hlt0, ⟨⟨hok, hA⟩, hC⟩, hK⟩ := h
  have hDig : Dig = pkF P.w (fun j => fld P.w Dig j) P.N := (pkF_fields hw Dig hlt0).symm
  have hF : ∀ j < P.N, fld P.w Dig j < 2 ^ P.w := fun j _ => Nat.mod_lt _ (by positivity)
  obtain ⟨⟨hXa, hXb, hXc, hXd⟩, hxs⟩ := run_sound8 P hw16 hwL hΔ hO lm hDig hF P.L (le_refl _) hok
  have cst : ∀ x : GF8, sp x * ONES = pkF P.w (fun _ => sp x) P.N := fun x => by rw [hO, ← pkF_const]
  have inj := fun {f g : ℕ → GF8} (he : pkF P.w (fun j => sp (f j)) P.N = pkF P.w (fun _ => sp (g 0)) P.N) =>
    fun j hj => sp_inj (pkF_inj hw (fun j _ => spw (f j)) (fun _ _ => spw (g 0)) he j hj)
  have ea := inj (g := fun _ => a) (hXa.symm.trans (hA.trans (cst a)))
  have ec := inj (g := fun _ => c) (hXc.symm.trans (hC.trans (cst c)))
  intro j hj
  refine ⟨hxs j hj, ea j hj, ec j hj, fun hk => ?_, fun hk => ?_⟩
  · subst hk
    simp only [cond_true, Nat.beq_eq] at hK
    exact inj (g := fun _ => b) (hXb.symm.trans (hK.trans (cst b))) j hj
  · subst hk
    simp only [cond_false, Nat.beq_eq] at hK
    exact inj (g := fun _ => d) (hXd.symm.trans (hK.trans (cst d))) j hj

/-! ## `SL(2, GF8)` -/

section Group

variable {R : Type*} [CommRing R]

/-- The entries of a matrix of `SL(2, R)`. -/
def ent (A : SpecialLinearGroup (Fin 2) R) : R × R × R × R := (A 0 0, A 0 1, A 1 0, A 1 1)

theorem det_entries' (A : SpecialLinearGroup (Fin 2) R) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rw [det_fin_two] at h
  exact h

theorem inv_entries' (A : SpecialLinearGroup (Fin 2) R) :
    A⁻¹ 0 0 = A 1 1 ∧ A⁻¹ 0 1 = -A 0 1 ∧ A⁻¹ 1 0 = -A 1 0 ∧ A⁻¹ 1 1 = A 0 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [SpecialLinearGroup.coe_inv, adjugate_fin_two]

theorem ent_mul (A B : SpecialLinearGroup (Fin 2) R) : ∀ i j : Fin 2,
    (A * B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  intro i j
  rw [SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_of_entries_c' [NoZeroDivisors R] {W X : SpecialLinearGroup (Fin 2) R} (hc : X 1 0 ≠ 0)
    (h00 : W 0 0 = X 0 0) (h10 : W 1 0 = X 1 0) (h11 : W 1 1 = X 1 1) : W = X := by
  have hW := det_entries' W
  have hX := det_entries' X
  rw [h00, h10, h11] at hW
  have h01 : W 0 1 = X 0 1 := by
    have : (W 0 1 - X 0 1) * X 1 0 = 0 := by linear_combination hX - hW
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hc
  apply SpecialLinearGroup.ext
  intro i j; fin_cases i <;> fin_cases j
  exacts [h00, h01, h10, h11]

theorem a_ne_of_c' [Nontrivial R] (A : SpecialLinearGroup (Fin 2) R) (h : A 1 0 = 0) : A 0 0 ≠ 0 := by
  have hdet := det_entries' A
  rw [h, mul_zero, sub_zero] at hdet
  intro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet

theorem eq_of_entries_nc' [NoZeroDivisors R] [Nontrivial R] {W X : SpecialLinearGroup (Fin 2) R} (hc : X 1 0 = 0)
    (h00 : W 0 0 = X 0 0) (h01 : W 0 1 = X 0 1) (h10 : W 1 0 = 0) : W = X := by
  have hW := det_entries' W
  have hX := det_entries' X
  rw [h00, h01, h10] at hW
  rw [hc] at hX
  have h11 : W 1 1 = X 1 1 := by
    have : X 0 0 * (W 1 1 - X 1 1) = 0 := by linear_combination hW - hX
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (a_ne_of_c' X hc)
    · exact sub_eq_zero.mp h
  apply SpecialLinearGroup.ext
  intro i j; fin_cases i <;> fin_cases j
  exacts [h00, h01, h10.trans hc.symm, h11]

end Group

instance : Nontrivial GF8 := ⟨⟨0, 1, by decide⟩⟩

/-- The matrix with entries `q` if its determinant is `1` (else the identity). -/
def mkSL8 (q : Q8) : SpecialLinearGroup (Fin 2) GF8 :=
  if h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1 then ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩
  else 1

/-- The inverse's entries (characteristic 2: `-x = x`). -/
def invQ (q : Q8) : Q8 := (q.2.2.2, q.2.1, q.2.2.1, q.1)

theorem neg8 (x : GF8) : -x = x := rfl

theorem ent_mkSL8 {q : Q8} (h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1) : ent (mkSL8 q) = q := by
  have e : mkSL8 q = ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩ := dif_pos h
  rw [e]
  rfl

variable (s2 : ℕ → SpecialLinearGroup (Fin 2) GF8) (invAt : ℕ → Bool)

/-- The letter table `lm` gives the entries of the letters. -/
def LetRep8 (Δ L : ℕ) (lm : ℕ → ℕ → Q8) : Prop :=
  ∀ t < L, ∀ u < Δ, lm t u = ent (letterX s2 invAt t u)

theorem letRep8_of (Δ L : ℕ) (gm : ℕ → Q8) (hs : ∀ u < Δ, s2 u = mkSL8 (gm u))
    (hdet : ∀ u < Δ, (gm u).1 * (gm u).2.2.2 - (gm u).2.1 * (gm u).2.2.1 = 1) (lm : ℕ → ℕ → Q8)
    (hlm : ∀ t u, lm t u = cond (invAt t) (invQ (gm u)) (gm u)) : LetRep8 s2 invAt Δ L lm := by
  intro t _ u hu
  have he := ent_mkSL8 (hdet u hu)
  rw [hlm, letterX, hs u hu]
  cases invAt t
  · exact he.symm
  · show invQ (gm u) = ent (mkSL8 (gm u))⁻¹
    obtain ⟨i00, i01, i10, i11⟩ := inv_entries' (mkSL8 (gm u))
    have e00 : (mkSL8 (gm u)) 0 0 = (gm u).1 := congrArg (fun x => x.1) he
    have e01 : (mkSL8 (gm u)) 0 1 = (gm u).2.1 := congrArg (fun x => x.2.1) he
    have e10 : (mkSL8 (gm u)) 1 0 = (gm u).2.2.1 := congrArg (fun x => x.2.2.1) he
    have e11 : (mkSL8 (gm u)) 1 1 = (gm u).2.2.2 := congrArg (fun x => x.2.2.2) he
    show _ = ((mkSL8 (gm u))⁻¹ 0 0, (mkSL8 (gm u))⁻¹ 0 1, (mkSL8 (gm u))⁻¹ 1 0, (mkSL8 (gm u))⁻¹ 1 1)
    rw [i00, i01, i10, i11, neg8, neg8, e00, e01, e10, e11]
    rfl

theorem semG_rep {Δ L : ℕ} {lm : ℕ → ℕ → Q8} (hrep : LetRep8 s2 invAt Δ L lm) (dg : ℕ → ℕ) :
    ∀ t ≤ L, (∀ t' < t, dg t' < Δ) → semG lm dg t = ent (wordX s2 invAt dg t) := by
  intro t
  induction t with
  | zero =>
    intro _ _
    simp [semG, wordX, ent]
  | succ t ih =>
    intro ht hdg
    rw [semG, ih (by omega) (fun t' h => hdg t' (by omega)), hrep t (by omega) (dg t) (hdg t (by omega)),
      wordX_succ]
    unfold mulQ ent
    rw [ent_mul, ent_mul, ent_mul, ent_mul]

/-! ## The second factor -/

/-- The batch of a matrix of `SL(2, GF8)` (as `bS`, with codes). -/
def bS8 (A : SpecialLinearGroup (Fin 2) GF8) : ℕ :=
  if A 1 0 = 0 then 8 * 7 + (code (A 0 0) - 1) else code (A 0 0) * 7 + (code (A 1 0) - 1)

/-- The free entry of a matrix in its batch. -/
def jS8 (A : SpecialLinearGroup (Fin 2) GF8) : ℕ := if A 1 0 = 0 then code (A 0 1) else code (A 1 1)

theorem code_pos {x : GF8} (h : x ≠ 0) : 1 ≤ code x := by
  rcases Nat.eq_zero_or_pos (code x) with h0 | h0
  · exact absurd (by rw [← mk_code x, h0]; rfl) h
  · exact h0

theorem bS8_lt (A : SpecialLinearGroup (Fin 2) GF8) : bS8 A < 8 * 8 - 1 := by
  unfold bS8
  split_ifs with hc
  · exact (bat_nc (by norm_num) (code_pos (a_ne_of_c' A hc)) (code_lt _)).2.2.2
  · exact (bat_c (by norm_num) (code_lt _) (code_pos hc) (code_lt _)).2.2.2

theorem jS8_lt (A : SpecialLinearGroup (Fin 2) GF8) : jS8 A < 8 := by
  unfold jS8; split_ifs <;> exact code_lt _

/-- A word that meets the constant targets of `A`'s batch at some slot has matrix `A`. -/
theorem word_const8 (P : Prm) (hw16 : 16 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) {lm : ℕ → ℕ → Q8} (hrep : LetRep8 s2 invAt P.Δ P.L lm)
    (A : SpecialLinearGroup (Fin 2) GF8) {Dig : ℕ}
    (h : batchOK8 P ONES lm Dig (kindB 8 (bS8 A)) (sp (mk (aB 8 (bS8 A))) * ONES) (sp (mk (jS8 A)) * ONES)
      (sp (mk (cB 8 (bS8 A))) * ONES) (sp (mk (jS8 A)) * ONES) = true)
    {j : ℕ} (hj : j < P.N) : wordX s2 invAt (digit (fld P.w Dig j)) P.L = A := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_nc (p := 8) (by norm_num) (code_pos (a_ne_of_c' A hc)) (code_lt (A 0 0))
    have eb : bS8 A = 8 * (8 - 1) + (code (A 0 0) - 1) := by unfold bS8; rw [if_pos hc]
    have ej : jS8 A = code (A 0 1) := by unfold jS8; rw [if_pos hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, mb, -⟩ := batch_sound8 P hw16 hwL hΔ hO lm h j hj
    have e := semG_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have mb' := mb rfl
    rw [e, mk_code] at ma mb'
    rw [e] at mc
    exact eq_of_entries_nc' hc ma mb' mc
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_c (p := 8) (by norm_num) (code_lt (A 0 0)) (code_pos hc) (code_lt (A 1 0))
    have eb : bS8 A = code (A 0 0) * (8 - 1) + (code (A 1 0) - 1) := by unfold bS8; rw [if_neg hc]
    have ej : jS8 A = code (A 1 1) := by unfold jS8; rw [if_neg hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, -, md⟩ := batch_sound8 P hw16 hwL hΔ hO lm h j hj
    have e := semG_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have md' := md rfl
    rw [e, mk_code] at ma mc md'
    exact eq_of_entries_c' hc ma mc md'

/-! ## The cover of `PSL(2,p) × Z_n × SL(2,8)` -/

variable {p n : ℕ}

/-- **The cover of `PSL(2,p) × Z_n × SL(2,8)`.** Batch `i` checks the first factor's sign-normalised batch
`i % B` and the constant targets of the second factor's batch `i / B / 8`, slot value `i / B % 8`. -/
theorem cover_prod8 [Fact p.Prime] [NeZero n] (hp2 : p ≠ 2) (sG₁ : ℕ → G p n) (P₁ : Prm) (hv₁ : P₁.valid)
    (hw16 : 16 ≤ P₁.w) (hpP : P₁.p = p) (hnP : P₁.n = n) (hN : P₁.N = p * n) {ONES RD NRD RZ : ℕ}
    (hO : ONES = pkF P₁.w (fun _ => 1) P₁.N) (hRD : RD = pkF P₁.w (fun j => j / P₁.n) P₁.N)
    (hNRD : NRD = pkF P₁.w (fun j => (P₁.p - j / P₁.n) % P₁.p) P₁.N) (hRZ : RZ = pkF P₁.w (fun j => j % P₁.n) P₁.N)
    {lt₁ : ℕ → ℕ → Let} {lm : ℕ → ℕ → Q8} (hlt₁ : LetOK P₁ lt₁) (hrep₁ : LetRep sG₁ invAt P₁.Δ P₁.L lt₁)
    (hrep₂ : LetRep8 s2 invAt P₁.Δ P₁.L lm)
    (hB : ∀ i < (8 * 8 - 1) * 8 * (p * hP p + hP p), ∃ Dig,
      batchOKpm P₁ ONES lt₁ Dig (kindBp p (i % (p * hP p + hP p))) (aBp p (i % (p * hP p + hP p)))
        (cBp p (i % (p * hP p + hP p))) RD NRD RZ = true ∧
      batchOK8 P₁ ONES lm Dig (kindB 8 (i / (p * hP p + hP p) / 8))
        (sp (mk (aB 8 (i / (p * hP p + hP p) / 8))) * ONES) (sp (mk (i / (p * hP p + hP p) % 8)) * ONES)
        (sp (mk (cB 8 (i / (p * hP p + hP p) / 8))) * ONES) (sp (mk (i / (p * hP p + hP p) % 8)) * ONES) = true) :
    ∀ x : PG p n × SpecialLinearGroup (Fin 2) GF8, ∃ dg : ℕ → ℕ, (∀ t < P₁.L, dg t < P₁.Δ) ∧
      wordX (fun u => (pi (sG₁ u), s2 u)) invAt dg P₁.L = x := by
  intro ⟨y₁, A₂⟩
  obtain ⟨x₁, rfl⟩ := pi_surj y₁
  have hv := hv₁
  obtain ⟨-, hwL, hΔ, -⟩ := hv
  have hB0 : 0 < p * hP p + hP p := by
    have : 1 ≤ hP p := by
      unfold hP
      have := p_two (p := p)
      rcases (Fact.out : p.Prime).eq_two_or_odd with h | h
      · exact absurd h hp2
      · omega
    nlinarith
  have hcov := cover_of_batches_pm_ex sG₁ invAt hp2 P₁ hv₁ hpP hnP hN hO hRD hNRD hRZ hlt₁ hrep₁
    (fun Dig => batchOK8 P₁ ONES lm Dig (kindB 8 (bS8 A₂)) (sp (mk (aB 8 (bS8 A₂))) * ONES)
      (sp (mk (jS8 A₂)) * ONES) (sp (mk (cB 8 (bS8 A₂))) * ONES) (sp (mk (jS8 A₂)) * ONES) = true)
    (fun b hb => by
      rw [hpP] at hb ⊢
      obtain ⟨e1, e2, e3, e4⟩ := flat_index hB0 (by norm_num) (bS8_lt A₂) (jS8_lt A₂) hb
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
  · exact word_const8 s2 invAt P₁ hw16 hwL hΔ hO hrep₂ A₂ hE hjN

/-- The order of `PSL(2,p) × Z_n × SL(2,8)`, doubled. -/
theorem card_PG_SL8 [Fact p.Prime] [NeZero n] (hp2 : p ≠ 2) :
    Nat.card (PG p n × SpecialLinearGroup (Fin 2) GF8) * 2 = p * (p * p - 1) * n * 504 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := SpecialLinearGroup (Fin 2) GF8), card_SL8,
    ← card_PG (p := p) (n := n) hp2]
  ring

end BipartiteDD.LeanAll.HaarGF8
