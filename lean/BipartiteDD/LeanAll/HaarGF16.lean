import BipartiteDD.LeanAll.GF16
import BipartiteDD.LeanAll.HaarGF8

/-! # Packed checks over `GF(16)`, and Haar graphs of `Z_n × SL(2,16)`

The packed check over `GF16` is that of `HaarGF8.lean` with spaced codes four bits apart (`GF16.sp`, `red16`). A
cell `Z_n × SL(2,16)` is covered by batches that fix the matrix (constant targets, `word_const16`) and run over the
`n` values of the `Z_n` part; that part is checked by the `HaarSwar` batch check with identity letters over `ZMod 2`
(`batch_sound`, `semN_rep`), whose words' `Z_n` parts are the cell's (`cover16`). -/

namespace BipartiteDD.LeanAll.HaarGF16

open BipartiteDD.LeanAll BipartiteDD.LeanAll.GF16 BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.Swar
open BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.HaarPSL BipartiteDD.LeanAll.HaarProd BipartiteDD.LeanAll.HaarGF8
open Matrix

/-- Matrix entries `(a, b, c, d)` over `GF16`. -/
abbrev Q16 := GF16 × GF16 × GF16 × GF16

/-- A letter with spaced entries (no shift). -/
def spL16 (q : Q16) : Let := ⟨sp q.1, sp q.2.1, sp q.2.2.1, sp q.2.2.2, 0⟩

/-- The product of entry quadruples. -/
def mulQ16 (x l : Q16) : Q16 :=
  (x.1 * l.1 + x.2.1 * l.2.2.1, x.1 * l.2.1 + x.2.1 * l.2.2.2, x.2.2.1 * l.1 + x.2.2.2 * l.2.2.1,
    x.2.2.1 * l.2.1 + x.2.2.2 * l.2.2.2)

/-- What a slot with digits `dg` computes in `t` letters. -/
def semG16 (lm : ℕ → ℕ → Q16) (dg : ℕ → ℕ) : ℕ → Q16
  | 0 => (1, 0, 0, 1)
  | t + 1 => mulQ16 (semG16 lm dg t) (lm t (dg t))

section Comp

variable (P : Prm) (ONES : ℕ) (lm : ℕ → ℕ → Q16)

/-- Fieldwise `red1`. -/
def red16 (V : ℕ) : ℕ :=
  ((V &&& (4369 * ONES)) + ((V >>> 16) &&& ONES) * 17 + ((V >>> 20) &&& ONES) * 272 +
    ((V >>> 24) &&& ONES) * 4352) &&& (4369 * ONES)

/-- One step over `GF16`. -/
def stepG16 (Dig t : ℕ) (X : St) : St × Bool :=
  let Dt := (Dig >>> (4 * t)) &&& (15 * ONES)
  let A := red16 ONES (selSum P ONES Dt (fun u => X.a * (spL16 (lm t u)).e + X.b * (spL16 (lm t u)).g) P.Δ)
  let Bq := red16 ONES (selSum P ONES Dt (fun u => X.a * (spL16 (lm t u)).f + X.b * (spL16 (lm t u)).h) P.Δ)
  let C := red16 ONES (selSum P ONES Dt (fun u => X.c * (spL16 (lm t u)).e + X.d * (spL16 (lm t u)).g) P.Δ)
  let D := red16 ONES (selSum P ONES Dt (fun u => X.c * (spL16 (lm t u)).f + X.d * (spL16 (lm t u)).h) P.Δ)
  (⟨A, Bq, C, D, 0⟩, Nat.beq (thr ONES Dt P.Δ) 0)

/-- The first `t` steps. -/
def runG16 (Dig t : ℕ) : St × Bool :=
  Nat.rec (motive := fun _ => St × Bool) (⟨ONES, 0, 0, ONES, 0⟩, true)
    (fun t acc => let r := stepG16 P ONES lm Dig t acc.1; (r.1, acc.2 && r.2)) t

/-- The batch check over `GF16`: the certificate fits, the digits are letters, and the final entries are the targets
(`a`, `c` and, by `kind`, `b` or `d`). -/
def batchOK16 (Dig : ℕ) (kind : Bool) (TA TB TC TD : ℕ) : Bool :=
  Nat.blt Dig (2 ^ (P.w * P.N)) &&
    ((runG16 P ONES lm Dig P.L).2 && Nat.beq (runG16 P ONES lm Dig P.L).1.a TA &&
      Nat.beq (runG16 P ONES lm Dig P.L).1.c TC &&
      cond kind (Nat.beq (runG16 P ONES lm Dig P.L).1.b TB) (Nat.beq (runG16 P ONES lm Dig P.L).1.d TD))

end Comp

/-- `X` packs the spaced codes of the slot states `xs`. -/
def Rep16 (P : Prm) (X : St) (xs : ℕ → Q16) : Prop :=
  X.a = pkF P.w (fun j => sp (xs j).1) P.N ∧ X.b = pkF P.w (fun j => sp (xs j).2.1) P.N ∧
  X.c = pkF P.w (fun j => sp (xs j).2.2.1) P.N ∧ X.d = pkF P.w (fun j => sp (xs j).2.2.2) P.N

theorem red16_eq {w N : ℕ} (hw : 29 ≤ w) {ONES V : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF w v N) (hv : ∀ j < N, v j < 2 ^ 28) : red16 ONES V = pkF w (fun j => red1 (v j)) N := by
  have hw0 : 0 < w := by omega
  have h28 : (2 : ℕ) ^ 28 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvw : ∀ j < N, v j < 2 ^ w := fun j hj => lt_of_lt_of_le (hv j hj) h28
  have cM : (4369 : ℕ) < 2 ^ w := lt_of_lt_of_le (by norm_num) h28
  have e1 : V &&& (4369 * ONES) = pkF w (fun j => v j &&& 4369) N := by
    rw [hV, hO, ← pkF_const, pkF_land hw0 hvw (fun _ _ => cM)]
  have e2 : (V >>> 16) &&& ONES = pkF w (fun j => (v j >>> 16) &&& 1) N := by
    rw [hV, hO, pkF_shr_land hw0 (by omega) (Nat.one_lt_two_pow (by omega)) hvw]
  have e3 : (V >>> 20) &&& ONES = pkF w (fun j => (v j >>> 20) &&& 1) N := by
    rw [hV, hO, pkF_shr_land hw0 (by omega) (Nat.one_lt_two_pow (by omega)) hvw]
  have e4 : (V >>> 24) &&& ONES = pkF w (fun j => (v j >>> 24) &&& 1) N := by
    rw [hV, hO, pkF_shr_land hw0 (by omega) (Nat.one_lt_two_pow (by omega)) hvw]
  have hs : ∀ j < N, (v j &&& 4369) + ((v j >>> 16) &&& 1) * 17 + ((v j >>> 20) &&& 1) * 272 +
      ((v j >>> 24) &&& 1) * 4352 < 2 ^ w := by
    intro j _
    have a1 : v j &&& 4369 ≤ 4369 := Nat.and_le_right
    have a2 : (v j >>> 16) &&& 1 ≤ 1 := Nat.and_le_right
    have a3 : (v j >>> 20) &&& 1 ≤ 1 := Nat.and_le_right
    have a4 : (v j >>> 24) &&& 1 ≤ 1 := Nat.and_le_right
    have : (v j &&& 4369) + ((v j >>> 16) &&& 1) * 17 + ((v j >>> 20) &&& 1) * 272 +
        ((v j >>> 24) &&& 1) * 4352 ≤ 9010 := by omega
    exact lt_of_le_of_lt this (lt_of_lt_of_le (by norm_num) h28)
  unfold red16
  rw [e1, e2, e3, e4, mul_comm _ 17, mul_comm _ 272, mul_comm _ 4352, ← pkF_mul, ← pkF_mul, ← pkF_mul, ← pkF_add,
    ← pkF_add, ← pkF_add, hO, ← pkF_const,
    pkF_land hw0 (fun j hj => by have := hs j hj; simpa [mul_comm] using this) (fun _ _ => cM)]
  exact pkF_congr (fun j _ => by unfold red1; ring_nf)

theorem lin_eq16 {w N : ℕ} {X Y : ℕ} {x y : ℕ → GF16} (hX : X = pkF w (fun j => sp (x j)) N)
    (hY : Y = pkF w (fun j => sp (y j)) N) (e g : GF16) :
    X * sp e + Y * sp g = pkF w (fun j => sp (x j) * sp e + sp (y j) * sp g) N :=
  lin_eq hX hY (sp e) (sp g)

theorem step_sound16 (P : Prm) (hw29 : 29 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q16) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) {t : ℕ} (ht : t < P.L) {X : St} {xs : ℕ → Q16}
    (hX : Rep16 P X xs) (hok : (stepG16 P ONES lm Dig t X).2 = true) :
    Rep16 P (stepG16 P ONES lm Dig t X).1 (fun j => mulQ16 (xs j) (lm t (digit (F j) t))) ∧
      ∀ j < P.N, digit (F j) t < P.Δ := by
  obtain ⟨hXa, hXb, hXc, hXd⟩ := hX
  have hw8 : 8 ≤ P.w := by omega
  have hw : 0 < P.w := by omega
  have hD := dig_eq hw hO hDig hF (t := t) (by omega)
  have hdt : ∀ j < P.N, (fun j => (F j >>> (4 * t)) &&& 15) j < 16 := fun j _ => digit_lt (F j) t
  simp only [stepG16, Nat.beq_eq] at hok
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
  have h28 : (2 : ℕ) ^ 28 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have entry : ∀ (Xu Xv : ℕ) (xu xv : ℕ → GF16), Xu = pkF P.w (fun j => sp (xu j)) P.N →
      Xv = pkF P.w (fun j => sp (xv j)) P.N → (E G : ℕ → GF16) →
      red16 ONES (selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ) =
        pkF P.w (fun j => sp (xu j * E (digit (F j) t) + xv j * G (digit (F j) t))) P.N := by
    intro Xu Xv xu xv hu hvv E G
    have hsel := selSum_eq P hw8 hO hD hdt (fun u => lin_eq16 hu hvv (E u) (G u)) hΔ
      (fun u _ j _ => lt_of_lt_of_le (lin_lt _ _ _ _) h28) P.Δ (le_refl _)
    have hsel' : selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ =
        pkF P.w (fun j => sp (xu j) * sp (E (digit (F j) t)) + sp (xv j) * sp (G (digit (F j) t))) P.N := by
      rw [hsel]
      exact pkF_congr (fun j hj => by simp only [digit] at hdΔ ⊢; simp [hdΔ j hj])
    rw [red16_eq hw29 hO hsel' (fun j _ => lin_lt _ _ _ _)]
    exact pkF_congr (fun j _ => red1_sp _ _ _ _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hdΔ⟩
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)

theorem run_sound16 (P : Prm) (hw29 : 29 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q16) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) :
    ∀ t ≤ P.L, (runG16 P ONES lm Dig t).2 = true →
      Rep16 P (runG16 P ONES lm Dig t).1 (fun j => semG16 lm (digit (F j)) t) ∧
        ∀ j < P.N, ∀ t' < t, digit (F j) t' < P.Δ := by
  intro t
  induction t with
  | zero =>
    intro _ _
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun j _ t' h => absurd h (by omega)⟩
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG16, sp_one])
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG16, sp_zero]), pkF_const, zero_mul]
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG16, sp_zero]), pkF_const, zero_mul]
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG16, sp_one])
  | succ t ih =>
    intro ht hok
    have e : runG16 P ONES lm Dig (t + 1) =
        ((stepG16 P ONES lm Dig t (runG16 P ONES lm Dig t).1).1,
          (runG16 P ONES lm Dig t).2 && (stepG16 P ONES lm Dig t (runG16 P ONES lm Dig t).1).2) := rfl
    rw [e] at hok ⊢
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hX, hxs⟩ := ih (by omega) hok.1
    obtain ⟨hY, hys⟩ := step_sound16 P hw29 hwL hΔ hO lm hDig hF (by omega) hX hok.2
    refine ⟨hY, fun j hj t' h => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact hxs j hj t' h
    · subst h; exact hys j hj

/-- **Soundness of a `GF16` batch with constant targets.** -/
theorem batch_sound16 (P : Prm) (hw29 : 29 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q16) {Dig : ℕ} {kind : Bool} {a b c d : GF16}
    (h : batchOK16 P ONES lm Dig kind (sp a * ONES) (sp b * ONES) (sp c * ONES) (sp d * ONES) = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semG16 lm (digit (fld P.w Dig j)) P.L).1 = a ∧ (semG16 lm (digit (fld P.w Dig j)) P.L).2.2.1 = c ∧
      (kind = true → (semG16 lm (digit (fld P.w Dig j)) P.L).2.1 = b) ∧
      (kind = false → (semG16 lm (digit (fld P.w Dig j)) P.L).2.2.2 = d) := by
  have hw : 0 < P.w := by omega
  have h28 : (2 : ℕ) ^ 28 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have spw : ∀ x : GF16, sp x < 2 ^ P.w := fun x => lt_of_lt_of_le (lt_trans (sp_lt x) (by norm_num)) h28
  unfold batchOK16 at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hlt0, ⟨⟨hok, hA⟩, hC⟩, hK⟩ := h
  have hDig : Dig = pkF P.w (fun j => fld P.w Dig j) P.N := (pkF_fields hw Dig hlt0).symm
  have hF : ∀ j < P.N, fld P.w Dig j < 2 ^ P.w := fun j _ => Nat.mod_lt _ (by positivity)
  obtain ⟨⟨hXa, hXb, hXc, hXd⟩, hxs⟩ := run_sound16 P hw29 hwL hΔ hO lm hDig hF P.L (le_refl _) hok
  have cst : ∀ x : GF16, sp x * ONES = pkF P.w (fun _ => sp x) P.N := fun x => by rw [hO, ← pkF_const]
  have inj := fun {f g : ℕ → GF16} (he : pkF P.w (fun j => sp (f j)) P.N = pkF P.w (fun _ => sp (g 0)) P.N) =>
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

instance : Nontrivial GF16 := ⟨⟨0, 1, by decide⟩⟩

/-- The matrix with entries `q` if its determinant is `1` (else the identity). -/
def mkSL16 (q : Q16) : SpecialLinearGroup (Fin 2) GF16 :=
  if h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1 then ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩
  else 1

/-- The inverse's entries (characteristic 2: `-x = x`). -/
def invQ16 (q : Q16) : Q16 := (q.2.2.2, q.2.1, q.2.2.1, q.1)

theorem neg16 (x : GF16) : -x = x := rfl

theorem ent_mkSL16 {q : Q16} (h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1) : ent (mkSL16 q) = q := by
  have e : mkSL16 q = ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩ := dif_pos h
  rw [e]
  rfl

variable (s2 : ℕ → SpecialLinearGroup (Fin 2) GF16) (invAt : ℕ → Bool)

/-- The letter table `lm` gives the entries of the letters. -/
def LetRep16 (Δ L : ℕ) (lm : ℕ → ℕ → Q16) : Prop :=
  ∀ t < L, ∀ u < Δ, lm t u = ent (letterX s2 invAt t u)

theorem letRep16_of (Δ L : ℕ) (gm : ℕ → Q16) (hs : ∀ u < Δ, s2 u = mkSL16 (gm u))
    (hdet : ∀ u < Δ, (gm u).1 * (gm u).2.2.2 - (gm u).2.1 * (gm u).2.2.1 = 1) (lm : ℕ → ℕ → Q16)
    (hlm : ∀ t u, lm t u = cond (invAt t) (invQ16 (gm u)) (gm u)) : LetRep16 s2 invAt Δ L lm := by
  intro t _ u hu
  have he := ent_mkSL16 (hdet u hu)
  rw [hlm, letterX, hs u hu]
  cases invAt t
  · exact he.symm
  · show invQ16 (gm u) = ent (mkSL16 (gm u))⁻¹
    obtain ⟨i00, i01, i10, i11⟩ := inv_entries' (mkSL16 (gm u))
    have e00 : (mkSL16 (gm u)) 0 0 = (gm u).1 := congrArg (fun x => x.1) he
    have e01 : (mkSL16 (gm u)) 0 1 = (gm u).2.1 := congrArg (fun x => x.2.1) he
    have e10 : (mkSL16 (gm u)) 1 0 = (gm u).2.2.1 := congrArg (fun x => x.2.2.1) he
    have e11 : (mkSL16 (gm u)) 1 1 = (gm u).2.2.2 := congrArg (fun x => x.2.2.2) he
    show _ = ((mkSL16 (gm u))⁻¹ 0 0, (mkSL16 (gm u))⁻¹ 0 1, (mkSL16 (gm u))⁻¹ 1 0, (mkSL16 (gm u))⁻¹ 1 1)
    rw [i00, i01, i10, i11, neg16, neg16, e00, e01, e10, e11]
    rfl

theorem semG16_rep {Δ L : ℕ} {lm : ℕ → ℕ → Q16} (hrep : LetRep16 s2 invAt Δ L lm) (dg : ℕ → ℕ) :
    ∀ t ≤ L, (∀ t' < t, dg t' < Δ) → semG16 lm dg t = ent (wordX s2 invAt dg t) := by
  intro t
  induction t with
  | zero =>
    intro _ _
    simp [semG16, wordX, ent]
  | succ t ih =>
    intro ht hdg
    rw [semG16, ih (by omega) (fun t' h => hdg t' (by omega)), hrep t (by omega) (dg t) (hdg t (by omega)),
      wordX_succ]
    unfold mulQ16 ent
    rw [ent_mul, ent_mul, ent_mul, ent_mul]

/-! ## The second factor -/

/-- The batch of a matrix of `SL(2, GF16)` (as `bS`, with codes). -/
def bS16 (A : SpecialLinearGroup (Fin 2) GF16) : ℕ :=
  if A 1 0 = 0 then 16 * 15 + (code (A 0 0) - 1) else code (A 0 0) * 15 + (code (A 1 0) - 1)

/-- The free entry of a matrix in its batch. -/
def jS16 (A : SpecialLinearGroup (Fin 2) GF16) : ℕ := if A 1 0 = 0 then code (A 0 1) else code (A 1 1)

theorem code_pos16 {x : GF16} (h : x ≠ 0) : 1 ≤ code x := by
  rcases Nat.eq_zero_or_pos (code x) with h0 | h0
  · exact absurd (by rw [← mk_code x, h0]; rfl) h
  · exact h0

theorem bS16_lt (A : SpecialLinearGroup (Fin 2) GF16) : bS16 A < 16 * 16 - 1 := by
  unfold bS16
  split_ifs with hc
  · exact (bat_nc (by norm_num) (code_pos16 (a_ne_of_c' A hc)) (code_lt _)).2.2.2
  · exact (bat_c (by norm_num) (code_lt _) (code_pos16 hc) (code_lt _)).2.2.2

theorem jS16_lt (A : SpecialLinearGroup (Fin 2) GF16) : jS16 A < 16 := by
  unfold jS16; split_ifs <;> exact code_lt _

/-- A word that meets the constant targets of `A`'s batch at some slot has matrix `A`. -/
theorem word_const16 (P : Prm) (hw29 : 29 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) {lm : ℕ → ℕ → Q16} (hrep : LetRep16 s2 invAt P.Δ P.L lm)
    (A : SpecialLinearGroup (Fin 2) GF16) {Dig : ℕ}
    (h : batchOK16 P ONES lm Dig (kindB 16 (bS16 A)) (sp (mk (aB 16 (bS16 A))) * ONES) (sp (mk (jS16 A)) * ONES)
      (sp (mk (cB 16 (bS16 A))) * ONES) (sp (mk (jS16 A)) * ONES) = true)
    {j : ℕ} (hj : j < P.N) : wordX s2 invAt (digit (fld P.w Dig j)) P.L = A := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_nc (p := 16) (by norm_num) (code_pos16 (a_ne_of_c' A hc)) (code_lt (A 0 0))
    have eb : bS16 A = 16 * (16 - 1) + (code (A 0 0) - 1) := by unfold bS16; rw [if_pos hc]
    have ej : jS16 A = code (A 0 1) := by unfold jS16; rw [if_pos hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, mb, -⟩ := batch_sound16 P hw29 hwL hΔ hO lm h j hj
    have e := semG16_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have mb' := mb rfl
    rw [e, mk_code] at ma mb'
    rw [e] at mc
    exact eq_of_entries_nc' hc ma mb' mc
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_c (p := 16) (by norm_num) (code_lt (A 0 0)) (code_pos16 hc) (code_lt (A 1 0))
    have eb : bS16 A = code (A 0 0) * (16 - 1) + (code (A 1 0) - 1) := by unfold bS16; rw [if_neg hc]
    have ej : jS16 A = code (A 1 1) := by unfold jS16; rw [if_neg hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, -, md⟩ := batch_sound16 P hw29 hwL hΔ hO lm h j hj
    have e := semG16_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have md' := md rfl
    rw [e, mk_code] at ma mc md'
    exact eq_of_entries_c' hc ma mc md'



/-! ## The cover of `Z_n × SL(2,16)` -/

theorem flat16 {b j : ℕ} (hb : b < 16 * 16 - 1) (hj : j < 16) :
    (b * 16 + j) / 16 = b ∧ (b * 16 + j) % 16 = j ∧ b * 16 + j < (16 * 16 - 1) * 16 := by omega

/-- **The cover of `Z_n × SL(2,16)`.** Batch `i` fixes the matrix of batch `i / 16` of `SL(2,16)` with free entry
`i % 16`; slot `j` is the `Z_n` value `j`, checked by the `HaarSwar` batch check over `ZMod 2` whose letters `sZ` have
identity matrices. -/
theorem cover16 {n : ℕ} [NeZero n] (sZ : ℕ → G 2 n) (P : Prm) (hv : P.valid) (hw29 : 29 ≤ P.w) (hnP : P.n = n)
    (hN : P.N = n) {ONES RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N) (hRZ : RZ = pkF P.w (fun j => j % n) P.N)
    {lt : ℕ → ℕ → Let} {lm : ℕ → ℕ → Q16} (hlt : LetOK P lt) (hrep₁ : LetRep sZ invAt P.Δ P.L lt)
    (hrep₂ : LetRep16 s2 invAt P.Δ P.L lm)
    (hB : ∀ i < (16 * 16 - 1) * 16, ∃ Dig, batchOK P ONES lt Dig true ONES 0 0 0 RZ = true ∧
      batchOK16 P ONES lm Dig (kindB 16 (i / 16)) (sp (mk (aB 16 (i / 16))) * ONES) (sp (mk (i % 16)) * ONES)
        (sp (mk (cB 16 (i / 16))) * ONES) (sp (mk (i % 16)) * ONES) = true) :
    ∀ x : Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF16, ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧
      wordX (fun u => ((sZ u).2, s2 u)) invAt dg P.L = x := by
  intro ⟨z, A⟩
  have hv' := hv
  obtain ⟨-, hwL, hΔ, -⟩ := hv'
  obtain ⟨e1, e2, hi⟩ := flat16 (bS16_lt A) (jS16_lt A)
  obtain ⟨Dig, h1, h2⟩ := hB _ hi
  rw [e1, e2] at h2
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hzv := ZMod.val_lt (Multiplicative.toAdd z)
  obtain ⟨j, hj⟩ : ∃ j, j = (Multiplicative.toAdd z).val := ⟨_, rfl⟩
  have hjN : j < P.N := by rw [hN, hj]; exact hzv
  have hw : 1 ≤ P.w := by omega
  have h2w : (2 : ℕ) ≤ 2 ^ P.w := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) hw
  have hnw : n < 2 ^ P.w := by
    have := hv.2.2.2.2.2.2.2.1
    have h3 : 2 ^ (P.w - 1) ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hnP]; omega
  have h0 : (0 : ℕ) = pkF P.w (fun _ => 0) P.N := by rw [pkF_const]; simp
  have hb := batch_sound P hv hO hlt (ta := fun _ => 1) (tb := fun _ => 0) (tc := fun _ => 0) (td := fun _ => 0)
    (tz := fun j => j % n) hO h0 h0 h0 hRZ
    (fun j _ => ⟨by omega, by positivity, by positivity, by positivity, by
      have := Nat.mod_lt j hn0; omega⟩) h1 j hjN
  obtain ⟨hdg, -, -, mz, -, -⟩ := hb
  refine ⟨digit (fld P.w Dig j), hdg, ?_⟩
  obtain ⟨-, -, -, -, ez⟩ := semN_rep (p := 2) (n := n) sZ invAt hrep₁ _ P.L (le_refl _) hdg
  rw [hnP] at mz
  have Wz : (wordG sZ invAt (digit (fld P.w Dig j)) P.L).2 = z := by
    apply Multiplicative.toAdd.injective
    rw [← ez, cast_of_modEq mz, Nat.mod_eq_of_lt (by rw [hj]; exact hzv), hj, ZMod.natCast_zmod_val]
  rw [wordX_pair]
  refine Prod.ext ?_ (word_const16 s2 invAt P hw29 hwL hΔ hO hrep₂ A h2 hjN)
  show wordX (fun u => (sZ u).2) invAt (digit (fld P.w Dig j)) P.L = z
  rw [← Wz, ← wordX_wordG]
  exact (wordX_map sZ invAt (MonoidHom.snd _ _) _ _).symm

theorem card_Z_SL16 {n : ℕ} [NeZero n] :
    Fintype.card (Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF16) = n * 4080 := by
  rw [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card, card_SL16]

end BipartiteDD.LeanAll.HaarGF16
