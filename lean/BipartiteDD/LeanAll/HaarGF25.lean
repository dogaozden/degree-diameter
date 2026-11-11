import BipartiteDD.LeanAll.GF25
import BipartiteDD.LeanAll.HaarGF8

/-! # Packed checks over `GF(25)`, and Haar graphs of `Z_n × SL(2,25)`

The packed check over `GF25` is that of `HaarGF16.lean` with the codes `c₀ + 128 c₁` (`GF25.sp`) and the fieldwise
reduction `red25` (`GF25.red1`: coefficients `c₀ + 3 c₂` and `c₁` mod 5, by a multiply-high division). As there, a
cell `Z_n × SL(2,25)` is covered by batches that fix the matrix (constant targets, `word_const25`) and run over the
`n` values of the `Z_n` part; that part is checked by the `HaarSwar` batch check with identity letters over `ZMod 2`
(`batch_sound`, `semN_rep`), whose words' `Z_n` parts are the cell's (`cover25`). -/

namespace BipartiteDD.LeanAll.HaarGF25

open BipartiteDD.LeanAll BipartiteDD.LeanAll.GF25 BipartiteDD.LeanAll.HaarSwar BipartiteDD.LeanAll.Swar
open BipartiteDD.LeanAll.HaarSL BipartiteDD.LeanAll.HaarPSL BipartiteDD.LeanAll.HaarProd BipartiteDD.LeanAll.HaarGF8
open Matrix

/-- Matrix entries `(a, b, c, d)` over `GF25`. -/
abbrev Q25 := GF25 × GF25 × GF25 × GF25

/-- A letter with spaced entries (no shift). -/
def spL25 (q : Q25) : Let := ⟨sp q.1, sp q.2.1, sp q.2.2.1, sp q.2.2.2, 0⟩

/-- The product of entry quadruples. -/
def mulQ25 (x l : Q25) : Q25 :=
  (x.1 * l.1 + x.2.1 * l.2.2.1, x.1 * l.2.1 + x.2.1 * l.2.2.2, x.2.2.1 * l.1 + x.2.2.2 * l.2.2.1,
    x.2.2.1 * l.2.1 + x.2.2.2 * l.2.2.2)

/-- What a slot with digits `dg` computes in `t` letters. -/
def semG25 (lm : ℕ → ℕ → Q25) (dg : ℕ → ℕ) : ℕ → Q25
  | 0 => (1, 0, 0, 1)
  | t + 1 => mulQ25 (semG25 lm dg t) (lm t (dg t))

section Comp

variable (P : Prm) (ONES : ℕ) (lm : ℕ → ℕ → Q25)

/-- Fieldwise `red1`. -/
def red25 (V : ℕ) : ℕ :=
  let U0 := (V &&& (127 * ONES)) + 3 * ((V >>> 14) &&& (127 * ONES))
  let U1 := (V >>> 7) &&& (127 * ONES)
  (U0 - 5 * (((U0 * 205) >>> 10) &&& (1023 * ONES))) + 128 * (U1 - 5 * (((U1 * 205) >>> 10) &&& (1023 * ONES)))

/-- One step over `GF25`. -/
def stepG25 (Dig t : ℕ) (X : St) : St × Bool :=
  let Dt := (Dig >>> (4 * t)) &&& (15 * ONES)
  let A := red25 ONES (selSum P ONES Dt (fun u => X.a * (spL25 (lm t u)).e + X.b * (spL25 (lm t u)).g) P.Δ)
  let Bq := red25 ONES (selSum P ONES Dt (fun u => X.a * (spL25 (lm t u)).f + X.b * (spL25 (lm t u)).h) P.Δ)
  let C := red25 ONES (selSum P ONES Dt (fun u => X.c * (spL25 (lm t u)).e + X.d * (spL25 (lm t u)).g) P.Δ)
  let D := red25 ONES (selSum P ONES Dt (fun u => X.c * (spL25 (lm t u)).f + X.d * (spL25 (lm t u)).h) P.Δ)
  (⟨A, Bq, C, D, 0⟩, Nat.beq (thr ONES Dt P.Δ) 0)

/-- The first `t` steps. -/
def runG25 (Dig t : ℕ) : St × Bool :=
  Nat.rec (motive := fun _ => St × Bool) (⟨ONES, 0, 0, ONES, 0⟩, true)
    (fun t acc => let r := stepG25 P ONES lm Dig t acc.1; (r.1, acc.2 && r.2)) t

/-- The batch check over `GF25`: the certificate fits, the digits are letters, and the final entries are the targets
(`a`, `c` and, by `kind`, `b` or `d`). -/
def batchOK25 (Dig : ℕ) (kind : Bool) (TA TB TC TD : ℕ) : Bool :=
  Nat.blt Dig (2 ^ (P.w * P.N)) &&
    ((runG25 P ONES lm Dig P.L).2 && Nat.beq (runG25 P ONES lm Dig P.L).1.a TA &&
      Nat.beq (runG25 P ONES lm Dig P.L).1.c TC &&
      cond kind (Nat.beq (runG25 P ONES lm Dig P.L).1.b TB) (Nat.beq (runG25 P ONES lm Dig P.L).1.d TD))

end Comp

/-- `X` packs the spaced codes of the slot states `xs`. -/
def Rep25 (P : Prm) (X : St) (xs : ℕ → Q25) : Prop :=
  X.a = pkF P.w (fun j => sp (xs j).1) P.N ∧ X.b = pkF P.w (fun j => sp (xs j).2.1) P.N ∧
  X.c = pkF P.w (fun j => sp (xs j).2.2.1) P.N ∧ X.d = pkF P.w (fun j => sp (xs j).2.2.2) P.N

/-- `U * 205 >>> 10` masked, fieldwise, for fields `u j < 1024`. -/
theorem q5_pk {w N : ℕ} (hw : 24 ≤ w) {ONES : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {u : ℕ → ℕ}
    (hu : ∀ j < N, u j < 1024) :
    ((pkF w u N * 205) >>> 10) &&& (1023 * ONES) = pkF w (fun j => q5 (u j)) N := by
  have hw0 : 0 < w := by omega
  have h20 : (2 : ℕ) ^ 20 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm : ∀ j < N, u j * 205 < 2 ^ w := fun j hj =>
    lt_of_lt_of_le (by have := hu j hj; omega : u j * 205 < 2 ^ 20) h20
  have c1023 : (1023 : ℕ) < 2 ^ (w - 10) :=
    lt_of_lt_of_le (by norm_num : (1023 : ℕ) < 2 ^ 10) (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [mul_comm, ← pkF_mul, hO, ← pkF_const]
  rw [pkF_shr_land hw0 (by omega) c1023 (f := fun j => 205 * u j) (fun j hj => by rw [mul_comm]; exact hm j hj)]
  exact pkF_congr (fun j _ => by unfold q5; rw [mul_comm])

theorem red25_eq {w N : ℕ} (hw : 24 ≤ w) {ONES V : ℕ} (hO : ONES = pkF w (fun _ => 1) N) {v : ℕ → ℕ}
    (hV : V = pkF w v N) (hv : ∀ j < N, v j < 2 ^ 20) : red25 ONES V = pkF w (fun j => red1 (v j)) N := by
  have hw0 : 0 < w := by omega
  have h20 : (2 : ℕ) ^ 20 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvw : ∀ j < N, v j < 2 ^ w := fun j hj => lt_of_lt_of_le (hv j hj) h20
  have c127 : (127 : ℕ) < 2 ^ w := lt_of_lt_of_le (by norm_num) h20
  have c127' : ∀ s, s ≤ 14 → (127 : ℕ) < 2 ^ (w - s) := fun s hs =>
    lt_of_lt_of_le (by norm_num : (127 : ℕ) < 2 ^ 7) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have k127 : 127 * ONES = pkF w (fun _ => 127) N := by rw [hO, ← pkF_const]
  have e0 : V &&& (127 * ONES) = pkF w (fun j => v j &&& 127) N := by
    rw [hV, k127, pkF_land hw0 hvw (fun _ _ => c127)]
  have e1 : (V >>> 7) &&& (127 * ONES) = pkF w (fun j => (v j >>> 7) &&& 127) N := by
    rw [hV, k127, pkF_shr_land hw0 (by omega) (c127' 7 (by norm_num)) hvw]
  have e2 : (V >>> 14) &&& (127 * ONES) = pkF w (fun j => (v j >>> 14) &&& 127) N := by
    rw [hV, k127, pkF_shr_land hw0 (by omega) (c127' 14 (by norm_num)) hvw]
  have eU0 : (V &&& (127 * ONES)) + 3 * ((V >>> 14) &&& (127 * ONES)) =
      pkF w (fun j => (v j &&& 127) + 3 * ((v j >>> 14) &&& 127)) N := by
    rw [e0, e2, ← pkF_mul, ← pkF_add]
  have u0 : ∀ j < N, (v j &&& 127) + 3 * ((v j >>> 14) &&& 127) < 1024 := fun j _ => by
    have a1 : v j &&& 127 ≤ 127 := Nat.and_le_right
    have a2 : (v j >>> 14) &&& 127 ≤ 127 := Nat.and_le_right
    omega
  have u1 : ∀ j < N, (v j >>> 7) &&& 127 < 1024 := fun j _ => by
    have a1 : (v j >>> 7) &&& 127 ≤ 127 := Nat.and_le_right
    omega
  have sub5 : ∀ u, u < 1024 → 5 * q5 u ≤ u := fun u hu => by rw [q5_eq u hu]; exact Nat.mul_div_le u 5
  dsimp only [red25]
  rw [eU0, e1, q5_pk hw hO u0, q5_pk hw hO u1, ← pkF_mul, ← pkF_mul, ← pkF_sub (fun j hj => sub5 _ (u0 j hj)),
    ← pkF_sub (fun j hj => sub5 _ (u1 j hj)), ← pkF_mul, ← pkF_add]
  rfl

theorem lin_eq25 {w N : ℕ} {X Y : ℕ} {x y : ℕ → GF25} (hX : X = pkF w (fun j => sp (x j)) N)
    (hY : Y = pkF w (fun j => sp (y j)) N) (e g : GF25) :
    X * sp e + Y * sp g = pkF w (fun j => sp (x j) * sp e + sp (y j) * sp g) N :=
  lin_eq hX hY (sp e) (sp g)

theorem step_sound25 (P : Prm) (hw24 : 24 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q25) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) {t : ℕ} (ht : t < P.L) {X : St} {xs : ℕ → Q25}
    (hX : Rep25 P X xs) (hok : (stepG25 P ONES lm Dig t X).2 = true) :
    Rep25 P (stepG25 P ONES lm Dig t X).1 (fun j => mulQ25 (xs j) (lm t (digit (F j) t))) ∧
      ∀ j < P.N, digit (F j) t < P.Δ := by
  obtain ⟨hXa, hXb, hXc, hXd⟩ := hX
  have hw8 : 8 ≤ P.w := by omega
  have hw : 0 < P.w := by omega
  have hD := dig_eq hw hO hDig hF (t := t) (by omega)
  have hdt : ∀ j < P.N, (fun j => (F j >>> (4 * t)) &&& 15) j < 16 := fun j _ => digit_lt (F j) t
  simp only [stepG25, Nat.beq_eq] at hok
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
  have h20 : (2 : ℕ) ^ 20 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have entry : ∀ (Xu Xv : ℕ) (xu xv : ℕ → GF25), Xu = pkF P.w (fun j => sp (xu j)) P.N →
      Xv = pkF P.w (fun j => sp (xv j)) P.N → (E G : ℕ → GF25) →
      red25 ONES (selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ) =
        pkF P.w (fun j => sp (xu j * E (digit (F j) t) + xv j * G (digit (F j) t))) P.N := by
    intro Xu Xv xu xv hu hvv E G
    have hsel := selSum_eq P hw8 hO hD hdt (fun u => lin_eq25 hu hvv (E u) (G u)) hΔ
      (fun u _ j _ => lt_of_lt_of_le (lin_lt _ _ _ _) h20) P.Δ (le_refl _)
    have hsel' : selSum P ONES ((Dig >>> (4 * t)) &&& (15 * ONES)) (fun u => Xu * sp (E u) + Xv * sp (G u)) P.Δ =
        pkF P.w (fun j => sp (xu j) * sp (E (digit (F j) t)) + sp (xv j) * sp (G (digit (F j) t))) P.N := by
      rw [hsel]
      exact pkF_congr (fun j hj => by simp only [digit] at hdΔ ⊢; simp [hdΔ j hj])
    rw [red25_eq hw24 hO hsel' (fun j _ => lin_lt _ _ _ _)]
    exact pkF_congr (fun j _ => red1_sp _ _ _ _)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hdΔ⟩
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.a X.b _ _ hXa hXb (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).1) (fun u => (lm t u).2.2.1)
  · exact entry X.c X.d _ _ hXc hXd (fun u => (lm t u).2.1) (fun u => (lm t u).2.2.2)

theorem run_sound25 (P : Prm) (hw24 : 24 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q25) {Dig : ℕ} {F : ℕ → ℕ}
    (hDig : Dig = pkF P.w F P.N) (hF : ∀ j < P.N, F j < 2 ^ P.w) :
    ∀ t ≤ P.L, (runG25 P ONES lm Dig t).2 = true →
      Rep25 P (runG25 P ONES lm Dig t).1 (fun j => semG25 lm (digit (F j)) t) ∧
        ∀ j < P.N, ∀ t' < t, digit (F j) t' < P.Δ := by
  intro t
  induction t with
  | zero =>
    intro _ _
    refine ⟨⟨?_, ?_, ?_, ?_⟩, fun j _ t' h => absurd h (by omega)⟩
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG25, sp_one])
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG25, sp_zero]), pkF_const, zero_mul]
    · show 0 = _
      rw [pkF_congr (g := fun _ => 0) (fun j _ => by simp [semG25, sp_zero]), pkF_const, zero_mul]
    · show ONES = _; rw [hO]; exact pkF_congr (fun j _ => by simp [semG25, sp_one])
  | succ t ih =>
    intro ht hok
    have e : runG25 P ONES lm Dig (t + 1) =
        ((stepG25 P ONES lm Dig t (runG25 P ONES lm Dig t).1).1,
          (runG25 P ONES lm Dig t).2 && (stepG25 P ONES lm Dig t (runG25 P ONES lm Dig t).1).2) := rfl
    rw [e] at hok ⊢
    simp only [Bool.and_eq_true] at hok
    obtain ⟨hX, hxs⟩ := ih (by omega) hok.1
    obtain ⟨hY, hys⟩ := step_sound25 P hw24 hwL hΔ hO lm hDig hF (by omega) hX hok.2
    refine ⟨hY, fun j hj t' h => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | h
    · exact hxs j hj t' h
    · subst h; exact hys j hj

/-- **Soundness of a `GF25` batch with constant targets.** -/
theorem batch_sound25 (P : Prm) (hw24 : 24 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) (lm : ℕ → ℕ → Q25) {Dig : ℕ} {kind : Bool} {a b c d : GF25}
    (h : batchOK25 P ONES lm Dig kind (sp a * ONES) (sp b * ONES) (sp c * ONES) (sp d * ONES) = true) :
    ∀ j < P.N, (∀ t < P.L, digit (fld P.w Dig j) t < P.Δ) ∧
      (semG25 lm (digit (fld P.w Dig j)) P.L).1 = a ∧ (semG25 lm (digit (fld P.w Dig j)) P.L).2.2.1 = c ∧
      (kind = true → (semG25 lm (digit (fld P.w Dig j)) P.L).2.1 = b) ∧
      (kind = false → (semG25 lm (digit (fld P.w Dig j)) P.L).2.2.2 = d) := by
  have hw : 0 < P.w := by omega
  have h20 : (2 : ℕ) ^ 20 ≤ 2 ^ P.w := Nat.pow_le_pow_right (by norm_num) (by omega)
  have spw : ∀ x : GF25, sp x < 2 ^ P.w := fun x => lt_of_lt_of_le (lt_trans (sp_lt x) (by norm_num)) h20
  unfold batchOK25 at h
  simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨hlt0, ⟨⟨hok, hA⟩, hC⟩, hK⟩ := h
  have hDig : Dig = pkF P.w (fun j => fld P.w Dig j) P.N := (pkF_fields hw Dig hlt0).symm
  have hF : ∀ j < P.N, fld P.w Dig j < 2 ^ P.w := fun j _ => Nat.mod_lt _ (by positivity)
  obtain ⟨⟨hXa, hXb, hXc, hXd⟩, hxs⟩ := run_sound25 P hw24 hwL hΔ hO lm hDig hF P.L (le_refl _) hok
  have cst : ∀ x : GF25, sp x * ONES = pkF P.w (fun _ => sp x) P.N := fun x => by rw [hO, ← pkF_const]
  have inj := fun {f g : ℕ → GF25} (he : pkF P.w (fun j => sp (f j)) P.N = pkF P.w (fun _ => sp (g 0)) P.N) =>
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

instance : Nontrivial GF25 := ⟨⟨0, 1, by decide⟩⟩

/-- The matrix with entries `q` if its determinant is `1` (else the identity). -/
def mkSL25 (q : Q25) : SpecialLinearGroup (Fin 2) GF25 :=
  if h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1 then ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩
  else 1

/-- The inverse's entries. -/
def invQ25 (q : Q25) : Q25 := (q.2.2.2, -q.2.1, -q.2.2.1, q.1)

theorem ent_mkSL25 {q : Q25} (h : q.1 * q.2.2.2 - q.2.1 * q.2.2.1 = 1) : ent (mkSL25 q) = q := by
  have e : mkSL25 q = ⟨!![q.1, q.2.1; q.2.2.1, q.2.2.2], by rw [det_fin_two_of]; exact h⟩ := dif_pos h
  rw [e]
  rfl

variable (s2 : ℕ → SpecialLinearGroup (Fin 2) GF25) (invAt : ℕ → Bool)

/-- The letter table `lm` gives the entries of the letters. -/
def LetRep25 (Δ L : ℕ) (lm : ℕ → ℕ → Q25) : Prop :=
  ∀ t < L, ∀ u < Δ, lm t u = ent (letterX s2 invAt t u)

theorem letRep25_of (Δ L : ℕ) (gm : ℕ → Q25) (hs : ∀ u < Δ, s2 u = mkSL25 (gm u))
    (hdet : ∀ u < Δ, (gm u).1 * (gm u).2.2.2 - (gm u).2.1 * (gm u).2.2.1 = 1) (lm : ℕ → ℕ → Q25)
    (hlm : ∀ t u, lm t u = cond (invAt t) (invQ25 (gm u)) (gm u)) : LetRep25 s2 invAt Δ L lm := by
  intro t _ u hu
  have he := ent_mkSL25 (hdet u hu)
  rw [hlm, letterX, hs u hu]
  cases invAt t
  · exact he.symm
  · show invQ25 (gm u) = ent (mkSL25 (gm u))⁻¹
    obtain ⟨i00, i01, i10, i11⟩ := inv_entries' (mkSL25 (gm u))
    have e00 : (mkSL25 (gm u)) 0 0 = (gm u).1 := congrArg (fun x => x.1) he
    have e01 : (mkSL25 (gm u)) 0 1 = (gm u).2.1 := congrArg (fun x => x.2.1) he
    have e10 : (mkSL25 (gm u)) 1 0 = (gm u).2.2.1 := congrArg (fun x => x.2.2.1) he
    have e11 : (mkSL25 (gm u)) 1 1 = (gm u).2.2.2 := congrArg (fun x => x.2.2.2) he
    show _ = ((mkSL25 (gm u))⁻¹ 0 0, (mkSL25 (gm u))⁻¹ 0 1, (mkSL25 (gm u))⁻¹ 1 0, (mkSL25 (gm u))⁻¹ 1 1)
    rw [i00, i01, i10, i11, e00, e01, e10, e11]
    rfl

theorem semG25_rep {Δ L : ℕ} {lm : ℕ → ℕ → Q25} (hrep : LetRep25 s2 invAt Δ L lm) (dg : ℕ → ℕ) :
    ∀ t ≤ L, (∀ t' < t, dg t' < Δ) → semG25 lm dg t = ent (wordX s2 invAt dg t) := by
  intro t
  induction t with
  | zero =>
    intro _ _
    simp [semG25, wordX, ent]
  | succ t ih =>
    intro ht hdg
    rw [semG25, ih (by omega) (fun t' h => hdg t' (by omega)), hrep t (by omega) (dg t) (hdg t (by omega)),
      wordX_succ]
    unfold mulQ25 ent
    rw [ent_mul, ent_mul, ent_mul, ent_mul]

/-! ## The second factor -/

/-- The batch of a matrix of `SL(2, GF25)` (as `bS`, with codes). -/
def bS25 (A : SpecialLinearGroup (Fin 2) GF25) : ℕ :=
  if A 1 0 = 0 then 25 * 24 + (code (A 0 0) - 1) else code (A 0 0) * 24 + (code (A 1 0) - 1)

/-- The free entry of a matrix in its batch. -/
def jS25 (A : SpecialLinearGroup (Fin 2) GF25) : ℕ := if A 1 0 = 0 then code (A 0 1) else code (A 1 1)

theorem code_pos25 {x : GF25} (h : x ≠ 0) : 1 ≤ code x := by
  rcases Nat.eq_zero_or_pos (code x) with h0 | h0
  · exact absurd (by rw [← mk_code x, h0]; rfl) h
  · exact h0

theorem bS25_lt (A : SpecialLinearGroup (Fin 2) GF25) : bS25 A < 25 * 25 - 1 := by
  unfold bS25
  split_ifs with hc
  · exact (bat_nc (by norm_num) (code_pos25 (a_ne_of_c' A hc)) (code_lt _)).2.2.2
  · exact (bat_c (by norm_num) (code_lt _) (code_pos25 hc) (code_lt _)).2.2.2

theorem jS25_lt (A : SpecialLinearGroup (Fin 2) GF25) : jS25 A < 25 := by
  unfold jS25; split_ifs <;> exact code_lt _

/-- A word that meets the constant targets of `A`'s batch at some slot has matrix `A`. -/
theorem word_const25 (P : Prm) (hw24 : 24 ≤ P.w) (hwL : 4 * P.L + 4 ≤ P.w) (hΔ : P.Δ ≤ 16) {ONES : ℕ}
    (hO : ONES = pkF P.w (fun _ => 1) P.N) {lm : ℕ → ℕ → Q25} (hrep : LetRep25 s2 invAt P.Δ P.L lm)
    (A : SpecialLinearGroup (Fin 2) GF25) {Dig : ℕ}
    (h : batchOK25 P ONES lm Dig (kindB 25 (bS25 A)) (sp (mk (aB 25 (bS25 A))) * ONES) (sp (mk (jS25 A)) * ONES)
      (sp (mk (cB 25 (bS25 A))) * ONES) (sp (mk (jS25 A)) * ONES) = true)
    {j : ℕ} (hj : j < P.N) : wordX s2 invAt (digit (fld P.w Dig j)) P.L = A := by
  by_cases hc : A 1 0 = 0
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_nc (p := 25) (by norm_num) (code_pos25 (a_ne_of_c' A hc)) (code_lt (A 0 0))
    have eb : bS25 A = 25 * (25 - 1) + (code (A 0 0) - 1) := by unfold bS25; rw [if_pos hc]
    have ej : jS25 A = code (A 0 1) := by unfold jS25; rw [if_pos hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, mb, -⟩ := batch_sound25 P hw24 hwL hΔ hO lm h j hj
    have e := semG25_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have mb' := mb rfl
    rw [e, mk_code] at ma mb'
    rw [e] at mc
    exact eq_of_entries_nc' hc ma mb' mc
  · obtain ⟨hbk, haB, hcB, -⟩ := bat_c (p := 25) (by norm_num) (code_lt (A 0 0)) (code_pos25 hc) (code_lt (A 1 0))
    have eb : bS25 A = code (A 0 0) * (25 - 1) + (code (A 1 0) - 1) := by unfold bS25; rw [if_neg hc]
    have ej : jS25 A = code (A 1 1) := by unfold jS25; rw [if_neg hc]
    rw [eb, ej, hbk, haB, hcB] at h
    obtain ⟨hdg, ma, mc, -, md⟩ := batch_sound25 P hw24 hwL hΔ hO lm h j hj
    have e := semG25_rep s2 invAt hrep _ P.L (le_refl _) hdg
    have md' := md rfl
    rw [e, mk_code] at ma mc md'
    exact eq_of_entries_c' hc ma mc md'



/-! ## The cover of `Z_n × SL(2,25)` -/

theorem flat25 {b j : ℕ} (hb : b < 25 * 25 - 1) (hj : j < 25) :
    (b * 25 + j) / 25 = b ∧ (b * 25 + j) % 25 = j ∧ b * 25 + j < (25 * 25 - 1) * 25 := by omega

/-- **The cover of `Z_n × SL(2,25)`.** Batch `i` fixes the matrix of batch `i / 25` of `SL(2,25)` with free entry
`i % 25`; slot `j` is the `Z_n` value `j`, checked by the `HaarSwar` batch check over `ZMod 2` whose letters `sZ` have
identity matrices. -/
theorem cover25 {n : ℕ} [NeZero n] (sZ : ℕ → G 2 n) (P : Prm) (hv : P.valid) (hw24 : 24 ≤ P.w) (hnP : P.n = n)
    (hN : P.N = n) {ONES RZ : ℕ} (hO : ONES = pkF P.w (fun _ => 1) P.N) (hRZ : RZ = pkF P.w (fun j => j % n) P.N)
    {lt : ℕ → ℕ → Let} {lm : ℕ → ℕ → Q25} (hlt : LetOK P lt) (hrep₁ : LetRep sZ invAt P.Δ P.L lt)
    (hrep₂ : LetRep25 s2 invAt P.Δ P.L lm)
    (hB : ∀ i < (25 * 25 - 1) * 25, ∃ Dig, batchOK P ONES lt Dig true ONES 0 0 0 RZ = true ∧
      batchOK25 P ONES lm Dig (kindB 25 (i / 25)) (sp (mk (aB 25 (i / 25))) * ONES) (sp (mk (i % 25)) * ONES)
        (sp (mk (cB 25 (i / 25))) * ONES) (sp (mk (i % 25)) * ONES) = true) :
    ∀ x : Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF25, ∃ dg : ℕ → ℕ, (∀ t < P.L, dg t < P.Δ) ∧
      wordX (fun u => ((sZ u).2, s2 u)) invAt dg P.L = x := by
  intro ⟨z, A⟩
  have hv' := hv
  obtain ⟨-, hwL, hΔ, -⟩ := hv'
  obtain ⟨e1, e2, hi⟩ := flat25 (bS25_lt A) (jS25_lt A)
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
  refine Prod.ext ?_ (word_const25 s2 invAt P hw24 hwL hΔ hO hrep₂ A h2 hjN)
  show wordX (fun u => (sZ u).2) invAt (digit (fld P.w Dig j)) P.L = z
  rw [← Wz, ← wordX_wordG]
  exact (wordX_map sZ invAt (MonoidHom.snd _ _) _ _).symm

theorem card_Z_SL25 {n : ℕ} [NeZero n] :
    Fintype.card (Multiplicative (ZMod n) × SpecialLinearGroup (Fin 2) GF25) = n * 15600 := by
  rw [Fintype.card_prod, Fintype.card_multiplicative, ZMod.card, card_SL25]

end BipartiteDD.LeanAll.HaarGF25
