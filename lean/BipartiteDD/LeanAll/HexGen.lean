import BipartiteDD.LeanAll.HexLocal

/-! # Hexagon constructions at diameter 7 from local certificates, over any finite field

`HexLocal` for a finite field `F` given with a `Coder`: a way to write vectors of `F⁷` as numbers, with Boolean
checks (a normalised point of the quadric; a hexagon pair with normalised Plücker coordinates; a linear combination)
and a code for lines, each with the lemma that makes it sound. `main` is `HexLocal.main` with `ZMod p` replaced by
`F` and `p` by `q = |F|`; the proof is the same. Coders: `HexLocal`'s arithmetic for `ZMod p`, and `HexGF8` for
`GF(8)`. -/

namespace BipartiteDD.LeanAll.HexGen

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal
open SimpleGraph Finset Module Submodule
open scoped Classical

set_option linter.unusedSectionVars false

/-- Vectors of `F⁷` written as numbers. -/
structure Coder (F : Type) [Field F] where
  vec : ℕ → V7 F
  ptB : ℕ → Bool
  pt_nrm : ∀ c, ptB c = true → Nrm (vec c)
  pt_q : ∀ c, ptB c = true → Qf (vec c) = 0
  pt_inj : ∀ c c', ptB c = true → ptB c' = true → vec c = vec c' → c = c'
  lnB : ℕ → ℕ → Bool
  ln_pair : ∀ a b, lnB a b = true → IsHPair (vec a) (vec b)
  ln_nrm : ∀ a b, lnB a b = true → Nrm (plV (vec a) (vec b))
  plC : ℕ → ℕ → ℕ
  pl_inj : ∀ a b a' b', plV (vec a) (vec b) = plV (vec a') (vec b') → plC a b = plC a' b'
  lin : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  lin_mem : ∀ y a b α β, lin y a b α β = true → vec y ∈ span F {vec a, vec b}

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {C : Coder F}

/-! ## Points and lines -/

theorem qf_rep' {v : V7 F} (hv : v ≠ 0) (hq : Qf v = 0) : Qf (Projectivization.mk F v hv).rep = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ v
    (Projectivization.mk F v hv).rep_nonzero hv).1 (Projectivization.mk_rep _)
  rw [← ha, Units.smul_def, Qf_smul, hq, mul_zero]

instance instNePt : Nonempty (SPt F) := by
  have h : Nat.card (SPt F) ≠ 0 := by
    rw [card_spt_eq]; positivity
  exact (Nat.card_ne_zero.1 h).1

instance instFinPt : Finite (SPt F) := Finite.of_injective (fun x : SPt F => x.1) Subtype.val_injective

instance instFinLn : Finite (HLine F) := HexagonEven.finite_hline_even

instance instNeLn : Nonempty (HLine F) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (SPt F))
  have h : Nat.card {W : HLine F // x.1.rep ∈ W.1} ≠ 0 := by
    rw [HexagonEven.card_lines_through_even]; omega
  obtain ⟨⟨W, -⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨W⟩

theorem Coder.ne_zero (C : Coder F) {a b : ℕ} (h : C.lnB a b = true) : C.vec a ≠ 0 := by
  intro h0
  have := (C.ln_nrm a b h).ne_zero
  rw [h0, plV_zero_left] at this
  exact this rfl

theorem Coder.not_mem (C : Coder F) {a b : ℕ} (h : C.lnB a b = true) : C.vec b ∉ span F {C.vec a} := by
  intro hm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hm
  have := (C.ln_nrm a b h).ne_zero
  rw [← ht, plV_smul_right] at this
  exact this rfl

/-- The point of a code. -/
noncomputable def ptOf (C : Coder F) (c : ℕ) : SPt F :=
  if h : C.ptB c = true then ⟨Projectivization.mk _ (C.vec c) (C.pt_nrm c h).ne_zero, qf_rep' _ (C.pt_q c h)⟩
  else Classical.arbitrary _

/-- The line of a basis. -/
noncomputable def lineOf (C : Coder F) (a b : ℕ) : HLine F :=
  if h : C.lnB a b = true then hlineOf (C.ne_zero h) (C.ln_pair a b h) (C.not_mem h) else Classical.arbitrary _

theorem lineOf_val {a b : ℕ} (h : C.lnB a b = true) : (lineOf C a b).1 = span F {C.vec a, C.vec b} := by
  rw [lineOf, dif_pos h]; rfl

theorem ptOf_rep_mem {c : ℕ} (h : C.ptB c = true) (W : Submodule F (V7 F)) :
    (ptOf C c).1.rep ∈ W ↔ C.vec c ∈ W := by
  simp only [ptOf, dif_pos h]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ (C.vec c)
    (Projectivization.mk F (C.vec c) (C.pt_nrm c h).ne_zero).rep_nonzero (C.pt_nrm c h).ne_zero).1
    (Projectivization.mk_rep _)
  rw [← ha]
  exact Submodule.smul_mem_iff_of_isUnit W a.isUnit

theorem inc_of_lin {y a b α β : ℕ} (hy : C.ptB y = true) (hl : C.lnB a b = true) (h : C.lin y a b α β = true) :
    hexInc (ptOf C y) (lineOf C a b) := by
  show (ptOf C y).1.rep ∈ (lineOf C a b).1
  rw [ptOf_rep_mem hy, lineOf_val hl]
  exact C.lin_mem y a b α β h

theorem inc_first {y b : ℕ} (hy : C.ptB y = true) (hl : C.lnB y b = true) : hexInc (ptOf C y) (lineOf C y b) := by
  show (ptOf C y).1.rep ∈ (lineOf C y b).1
  rw [ptOf_rep_mem hy, lineOf_val hl]
  exact subset_span (by simp)

theorem ptOf_inj {c c' : ℕ} (h : C.ptB c = true) (h' : C.ptB c' = true) (he : ptOf C c = ptOf C c') : c = c' := by
  simp only [ptOf, dif_pos h, dif_pos h', Subtype.mk.injEq] at he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff F _ _ (C.pt_nrm c h).ne_zero (C.pt_nrm c' h').ne_zero).1 he
  have : C.vec c = C.vec c' :=
    Nrm.eq_of_smul (C.pt_nrm c' h') (C.pt_nrm c h) (a := (a : F)) (by rw [← ha, Units.smul_def])
  exact C.pt_inj c c' h h' this

theorem lineOf_inj {a b a' b' : ℕ} (h : C.lnB a b = true) (h' : C.lnB a' b' = true)
    (he : lineOf C a b = lineOf C a' b') : C.plC a b = C.plC a' b' := by
  have hs := congrArg Subtype.val he
  rw [lineOf_val h, lineOf_val h'] at hs
  have ha' : C.vec a' ∈ span F {C.vec a, C.vec b} := by rw [hs]; exact subset_span (by simp)
  have hb' : C.vec b' ∈ span F {C.vec a, C.vec b} := by rw [hs]; exact subset_span (by simp)
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 ha'
  obtain ⟨u, w, huw⟩ := Submodule.mem_span_pair.1 hb'
  have hpl : plV (C.vec a') (C.vec b') = (s * w - t * u) • plV (C.vec a) (C.vec b) := by
    rw [← hst, ← huw, plV_comb]
  have := Nrm.eq_of_smul (C.ln_nrm a b h) (C.ln_nrm a' b' h') hpl
  exact C.pl_inj a b a' b' this.symm

theorem card_pts' (W : HLine F) : Nat.card {x : SPt F // hexInc x W} = Fintype.card F + 1 :=
  card_points_hline W

theorem card_lns' (x : SPt F) : Nat.card {W : HLine F // hexInc x W} = Fintype.card F + 1 :=
  HexagonEven.card_lines_through_even x

/-! ## The certificate of one freed point -/

/-- The check of a certificate at the domain point `ir` (`L0 = sg ir`). -/
def certOK (C : Coder F) (p M : ℕ) (ptc lnA lnB sg : ℕ → ℕ) (rflag : ℕ → Bool) (ir : ℕ) (c : Cert) : Bool :=
  Nat.beq (lenP c.1) (p + 1) &&
  sortedLt (c.1.map (fun e => C.plC (ptc ir) e.1)) &&
  allP (fun e => C.lnB (ptc ir) e.1 && Nat.beq (lenP e.2) p && sortedLt (e.2.map (·.1)) &&
    allP (fun t => Nat.blt t.1 M && !(Nat.beq t.1 ir) && !(rflag t.1) &&
      C.lin (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2) e.2) c.1 &&
  Nat.beq (lenP c.2) (p + 1) &&
  sortedLt (c.2.map (·.1.1)) &&
  allP (fun f => C.ptB f.1.1 && C.lin f.1.1 (lnA (sg ir)) (lnB (sg ir)) f.1.2.1 f.1.2.2 &&
    Nat.beq (lenP f.2) p && sortedLt (f.2.map (·.1)) &&
    allP (fun t => Nat.blt t.1 M && !(Nat.beq t.1 (sg ir)) &&
      C.lin f.1.1 (lnA t.1) (lnB t.1) t.2.1 t.2.2.1 && Nat.blt t.2.2.2 (p * (p + 1)) &&
      Nat.beq (sg ((c.1.flatMap (·.2)).getD t.2.2.2 (0, 0, 0)).1) t.1) f.2) c.2 &&
  Nat.beq (maskOf c.2) (2 ^ (p * (p + 1)) - 1)

/-- What a passing `certOK` says. -/
structure CertSpec (C : Coder F) (p M : ℕ) (ptc lnA lnB sg : ℕ → ℕ) (rflag : ℕ → Bool) (ir : ℕ) (c : Cert) : Prop where
  e0 : c.1.length = p + 1
  e1 : (c.1.map (fun e => C.plC (ptc ir) e.1)).Nodup
  e2 : ∀ e ∈ c.1, C.lnB (ptc ir) e.1 = true ∧ e.2.length = p ∧ (e.2.map (·.1)).Nodup ∧
    ∀ t ∈ e.2, t.1 < M ∧ t.1 ≠ ir ∧ rflag t.1 = false ∧ C.lin (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2 = true
  f0 : c.2.length = p + 1
  f1 : (c.2.map (·.1.1)).Nodup
  f2 : ∀ f ∈ c.2, C.ptB f.1.1 = true ∧ C.lin f.1.1 (lnA (sg ir)) (lnB (sg ir)) f.1.2.1 f.1.2.2 = true ∧
    f.2.length = p ∧ (f.2.map (·.1)).Nodup ∧
    ∀ t ∈ f.2, t.1 < M ∧ t.1 ≠ sg ir ∧ C.lin f.1.1 (lnA t.1) (lnB t.1) t.2.1 t.2.2.1 = true
  f3 : ∀ f ∈ c.2, ∀ t ∈ f.2, ∃ x ∈ c.1.flatMap (·.2), sg x.1 = t.1
  f4 : ∀ x ∈ c.1.flatMap (·.2), ∃ f ∈ c.2, ∃ t ∈ f.2, sg x.1 = t.1

theorem certSpec_of {M : ℕ} {ptc lnA lnB sg : ℕ → ℕ} {rflag : ℕ → Bool} {ir : ℕ} {c : Cert}
    (h : certOK C p M ptc lnA lnB sg rflag ir c = true) : CertSpec C p M ptc lnA lnB sg rflag ir c := by
  simp only [certOK, Bool.and_eq_true, Nat.beq_eq, allP_eq, lenP_eq, List.all_eq_true, Nat.blt_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hE0, hE1⟩, hE2⟩, hF0⟩, hF1⟩, hF2⟩, hM⟩ := h
  have hE2' : ∀ e ∈ c.1, C.lnB (ptc ir) e.1 = true ∧ e.2.length = p ∧ (e.2.map (·.1)).Nodup ∧
      ∀ t ∈ e.2, t.1 < M ∧ t.1 ≠ ir ∧ rflag t.1 = false ∧ C.lin (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2 = true := by
    intro e he
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hE2 e he
    exact ⟨h1, h2, nodup_of_sortedLt h3, fun t ht => by
      obtain ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩ := h4 t ht
      exact ⟨h5, fun h => by simp [h] at h6, by simpa using h7, h8⟩⟩
  have hlen : (c.1.flatMap (·.2)).length = p * (p + 1) := by
    rw [length_flatMap (k := p) (fun e he => (hE2' e he).2.1), hE0]; ring
  refine ⟨hE0, nodup_of_sortedLt hE1, hE2', hF0, nodup_of_sortedLt hF1, fun f hf => ?_, fun f hf t ht => ?_,
    fun x hx => ?_⟩
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hF2 f hf
    exact ⟨h1, h2, h3, nodup_of_sortedLt h4, fun t ht => by
      obtain ⟨⟨⟨⟨h6, h7⟩, h8⟩, -⟩, -⟩ := h5 t ht
      exact ⟨h6, fun h => by simp [h] at h7, h8⟩⟩
  · obtain ⟨-, h5⟩ := hF2 f hf
    obtain ⟨⟨-, h9⟩, h10⟩ := h5 t ht
    refine ⟨(c.1.flatMap (·.2)).getD t.2.2.2 (0, 0, 0), ?_, h10⟩
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact h9)]
    exact List.getElem_mem _
  · obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨f, hf, t, ht, hte⟩ := mem_of_mask hM e (by rw [← hlen]; exact he)
    obtain ⟨-, h5⟩ := hF2 f hf
    obtain ⟨-, h10⟩ := h5 t ht
    refine ⟨f, hf, t, ht, ?_⟩
    rw [hte, List.getD_eq_getElem _ _ he] at h10
    exact h10

/-! ## Gamma_2 of a freed point and of its line -/

section Gamma

variable {M : ℕ} {ptc lnA lnB sg : ℕ → ℕ} {rflag : ℕ → Bool}

/-- The domain points. -/
noncomputable def Fp (C : Coder F) (ptc : ℕ → ℕ) (i : ℕ) : SPt F := ptOf C (ptc i)

/-- The domain lines. -/
noncomputable def Gl (C : Coder F) (lnA lnB : ℕ → ℕ) (j : ℕ) : HLine F := lineOf C (lnA j) (lnB j)

/-- The global checks. -/
structure Glob (C : Coder F) (M : ℕ) (ptc lnA lnB sg sgi : ℕ → ℕ) : Prop where
  pt : ∀ i < M, C.ptB (ptc i) = true
  ptinc : ∀ i, i + 1 < M → ptc i < ptc (i + 1)
  ln : ∀ j < M, C.lnB (lnA j) (lnB j) = true
  lninc : ∀ j, j + 1 < M → C.plC (lnA j) (lnB j) < C.plC (lnA (j + 1)) (lnB (j + 1))
  sg : ∀ i < M, sg i < M ∧ sgi (sg i) = i

variable {sgi : ℕ → ℕ}

theorem Glob.fp_inj (hG : Glob C M ptc lnA lnB sg sgi) : ∀ i < M, ∀ j < M, Fp C ptc i = Fp C ptc j → i = j :=
  fun i hi j hj he => inj_of_succ hG.ptinc i hi j hj (ptOf_inj (hG.pt i hi) (hG.pt j hj) he)

theorem Glob.gl_inj (hG : Glob C M ptc lnA lnB sg sgi) : ∀ i < M, ∀ j < M, Gl C lnA lnB i = Gl C lnA lnB j → i = j :=
  fun i hi j hj he => inj_of_succ (f := fun j => C.plC (lnA j) (lnB j)) hG.lninc i hi j hj
    (lineOf_inj (hG.ln i hi) (hG.ln j hj) he)

/-- The points collinear with a freed point are the first list of its certificate. -/
theorem coll_iff (hG : Glob C M ptc lnA lnB sg sgi) {ir : ℕ} (hir : ir < M) {c : Cert}
    (hc : CertSpec C (Fintype.card F) M ptc lnA lnB sg rflag ir c) (y : SPt F) :
    Coll hexInc (Fp C ptc ir) y ↔ ∃ x ∈ c.1.flatMap (·.2), y = Fp C ptc x.1 := by
  have hr := hG.pt ir hir
  constructor
  · rintro ⟨hne, W, hrW, hyW⟩
    have hW : W ∈ c.1.map (fun e => lineOf C (ptc ir) e.1) := by
      refine mem_of_card (card_lns' (Fp C ptc ir)) _ (by rw [List.length_map, hc.e0]) ?_ ?_ W hrW
      · exact nodup_map_of hc.e1 (fun e he e' he' hee => lineOf_inj (hc.e2 e he).1 (hc.e2 e' he').1 hee)
      · intro W' hW'
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hW'
        exact inc_first hr (hc.e2 e he).1
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hW
    obtain ⟨hl, hlen, hnd, hent⟩ := hc.e2 e he
    have hy : y ∈ Fp C ptc ir :: e.2.map (fun t => Fp C ptc t.1) := by
      refine mem_of_card (card_pts' _) _ (by simp [hlen]) ?_ ?_ y hyW
      · refine List.nodup_cons.2 ⟨fun hm => ?_, ?_⟩
        · obtain ⟨t, ht, h⟩ := List.mem_map.1 hm
          exact (hent t ht).2.1 (hG.fp_inj _ (hent t ht).1 _ hir h)
        · exact nodup_map_of hnd (fun t ht t' ht' htt => hG.fp_inj _ (hent t ht).1 _ (hent t' ht').1 htt)
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact inc_first hr hl
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
          exact inc_of_lin (hG.pt _ (hent t ht).1) hl (hent t ht).2.2.2
    rcases List.mem_cons.1 hy with h | h
    · exact absurd h.symm hne
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      exact ⟨t, List.mem_flatMap.2 ⟨e, he, ht⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨e, he, ht⟩ := List.mem_flatMap.1 hx
    obtain ⟨hl, -, -, hent⟩ := hc.e2 e he
    refine ⟨fun h => (hent x ht).2.1 (hG.fp_inj _ (hent x ht).1 _ hir h.symm), lineOf C (ptc ir) e.1,
      inc_first hr hl, inc_of_lin (hG.pt _ (hent x ht).1) hl (hent x ht).2.2.2⟩

/-- The lines concurrent with `σ r` are the second list of the certificate. -/
theorem conc_iff (hG : Glob C M ptc lnA lnB sg sgi) {ir : ℕ} (hir : ir < M) {c : Cert}
    (hc : CertSpec C (Fintype.card F) M ptc lnA lnB sg rflag ir c) (W : HLine F) :
    Conc hexInc (Gl C lnA lnB (sg ir)) W ↔ ∃ f ∈ c.2, ∃ t ∈ f.2, W = Gl C lnA lnB t.1 := by
  have hL0 := (hG.sg ir hir).1
  have hl := hG.ln _ hL0
  constructor
  · rintro ⟨hne, x, hxl, hxW⟩
    have hx : x ∈ c.2.map (fun f => ptOf C f.1.1) := by
      refine mem_of_card (card_pts' _) _ (by rw [List.length_map, hc.f0]) ?_ ?_ x hxl
      · exact nodup_map_of hc.f1 (fun f hf f' hf' hff => ptOf_inj (hc.f2 f hf).1 (hc.f2 f' hf').1 hff)
      · intro x' hx'
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'
        exact inc_of_lin (hc.f2 f hf).1 hl (hc.f2 f hf).2.1
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hz, hzl, hlen, hnd, hent⟩ := hc.f2 f hf
    have hW : W ∈ Gl C lnA lnB (sg ir) :: f.2.map (fun t => Gl C lnA lnB t.1) := by
      refine mem_of_card (card_lns' _) _ (by simp [hlen]) ?_ ?_ W hxW
      · refine List.nodup_cons.2 ⟨fun hm => ?_, ?_⟩
        · obtain ⟨t, ht, h⟩ := List.mem_map.1 hm
          exact (hent t ht).2.1 (hG.gl_inj _ (hent t ht).1 _ hL0 h)
        · exact nodup_map_of hnd (fun t ht t' ht' htt => hG.gl_inj _ (hent t ht).1 _ (hent t' ht').1 htt)
      · intro W' hW'
        rcases List.mem_cons.1 hW' with rfl | hW'
        · exact inc_of_lin hz hl hzl
        · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hW'
          exact inc_of_lin hz (hG.ln _ (hent t ht).1) (hent t ht).2.2
    rcases List.mem_cons.1 hW with h | h
    · exact absurd h.symm hne
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
      exact ⟨f, hf, t, ht, rfl⟩
  · rintro ⟨f, hf, t, ht, rfl⟩
    obtain ⟨hz, hzl, -, -, hent⟩ := hc.f2 f hf
    exact ⟨fun h => (hent t ht).2.1 (hG.gl_inj _ (hent t ht).1 _ hL0 h.symm), ptOf C f.1.1,
      inc_of_lin hz hl hzl, inc_of_lin hz (hG.ln _ (hent t ht).1) (hent t ht).2.2⟩

end Gamma



/-! ## The hub graph (any degree bound) -/

/-- The search graph maps onto the hub graph. -/
def hubHom' {d m : ℕ} {hubL hubR : ℕ → List ℕ} (hHL : LocalSpec d (2 * m) (hubNb m hubL hubR) (hubCol m))
    (hH2 : ∀ u < m, ∀ v ∈ hubR u, v < m ∧ u ∈ hubL v) :
    graphF (2 * m) (hubNb m hubL hubR) →g hubGraph (NSof hubL (m := m)) where
  toFun := toHub m
  map_rel' := by
    intro a b hab
    have hb := (adj_iff hHL).1 hab
    simp only [hubNb] at hb
    by_cases ha : a.val < m
    · rw [show Nat.blt a.val m = true by simpa using ha] at hb
      simp only [cond_true, List.mem_map] at hb
      obtain ⟨u, hu, hbu⟩ := hb
      have hbm : ¬ b.val < m := by rw [← hbu]; change ¬ m + u < m; omega
      have hum : u < m := by have := b.isLt; rw [← hbu] at this; change m + u < 2 * m at this; omega
      have e1 : toHub m a = .inl ⟨a.val, ha⟩ := by simp [toHub, ha]
      have e2 : toHub m b = .inr ⟨u, hum⟩ := by
        simp only [toHub, hbm, dite_false, Sum.inr.injEq, Fin.mk.injEq]
        rw [← hbu]; change m + u - m = u; omega
      rw [e1, e2]
      exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inl hu⟩
    · rw [Bool.eq_false_iff.2 (fun hh => ha (ltOfBlt hh))] at hb
      simp only [Bool.cond_false] at hb
      have hb' : b.val ∈ hubR (a.val - m) := hb
      obtain ⟨hbm, hab'⟩ := hH2 (a.val - m) (by have := a.isLt; omega) b.val hb'
      have e1 : toHub m a = .inr ⟨a.val - m, by have := a.isLt; omega⟩ := by simp [toHub, ha]
      have e2 : toHub m b = .inl ⟨b.val, hbm⟩ := by simp [toHub, hbm]
      rw [e1, e2]
      exact (SimpleGraph.fromRel_adj _ _ _).2 ⟨by simp, Or.inr hab'⟩

theorem hub_reach' {d m : ℕ} {hubL hubR : ℕ → List ℕ}
    (hHL : LocalSpec d (2 * m) (hubNb m hubL hubR) (hubCol m))
    (hH2 : ∀ u < m, ∀ v ∈ hubR u, v < m ∧ u ∈ hubL v)
    (hHB : ∀ s (hs : s < 2 * m) (v : Fin (2 * m)), (graphF (2 * m) (hubNb m hubL hubR)).edist v ⟨s, hs⟩ ≤ 7)
    (a b : Fin (2 * m)) (hab : hubCol m a.val = hubCol m b.val) :
    Reach (hubGraph (NSof hubL (m := m))) (toHub m a) (toHub m b) 6 := by
  have he : (graphF (2 * m) (hubNb m hubL hubR)).edist a b ≤ 7 := hHB b.val b.isLt a
  have hne : (graphF (2 * m) (hubNb m hubL hubR)).edist a b ≠ ⊤ :=
    ne_top_of_le_ne_top (by exact ENat.coe_ne_top 7) he
  obtain ⟨w, hw⟩ := (SimpleGraph.edist_ne_top_iff_reachable.1 hne).exists_walk_length_eq_edist
  have h7 : w.length ≤ 7 := by
    have : (w.length : ℕ∞) ≤ 7 := hw ▸ he
    exact_mod_cast this
  have hev : Even w.length := (col_walk hHL w).1 hab
  have h6 : Reach (graphF (2 * m) (hubNb m hubL hubR)) a b 6 := ⟨w, by rcases hev with ⟨k, hk⟩; omega⟩
  exact Reach.map (hubHom' hHL hH2) h6



/-! ## The checks as Boolean functions -/

/-- Point `i` of the domain. -/
def gPt (C : Coder F) (M : ℕ) (ptc : ℕ → ℕ) (i : ℕ) : Bool :=
  C.ptB (ptc i) && (Nat.beq (i + 1) M || Nat.blt (ptc i) (ptc (i + 1)))

/-- Line `j` of the domain and `σ` at `j`. -/
def gLn (C : Coder F) (M : ℕ) (lnA lnB sg sgi : ℕ → ℕ) (j : ℕ) : Bool :=
  C.lnB (lnA j) (lnB j) &&
    (Nat.beq (j + 1) M || Nat.blt (C.plC (lnA j) (lnB j)) (C.plC (lnA (j + 1)) (lnB (j + 1)))) &&
    Nat.blt (sg j) M && Nat.beq (sgi (sg j)) j

theorem glob_of {M : ℕ} {ptc lnA lnB sg sgi : ℕ → ℕ} (h1 : ∀ i < M, gPt C M ptc i = true)
    (h2 : ∀ j < M, gLn C M lnA lnB sg sgi j = true) : Glob C M ptc lnA lnB sg sgi := by
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun j hj => ?_, fun j hj => ?_, fun i hi => ?_⟩
  · have := h1 i hi; simp only [gPt, Bool.and_eq_true] at this; exact this.1
  · have := h1 i (by omega); simp only [gPt, Bool.and_eq_true] at this; exact ltOfBlt (succ_of this.2 hi)
  · have := h2 j hj; simp only [gLn, Bool.and_eq_true] at this; exact this.1.1.1
  · have := h2 j (by omega); simp only [gLn, Bool.and_eq_true] at this; exact ltOfBlt (succ_of this.1.1.2 hj)
  · have := h2 i hi; simp only [gLn, Bool.and_eq_true, Nat.beq_eq] at this; exact ⟨ltOfBlt this.1.2, this.2⟩

theorem hub_of' {p m : ℕ} {hubL hubR : ℕ → List ℕ} (h : ∀ v < m, gH p m hubL hubR v = true) :
    (∀ v < m, ∀ u ∈ hubL v, u < m ∧ v ∈ hubR u) ∧ (∀ u < m, ∀ v ∈ hubR u, v < m ∧ u ∈ hubL v) ∧
    (∀ v < m, (hubL v).length ≤ p - 1) ∧ (∀ u < m, (hubR u).length ≤ p - 1) := by
  have key : ∀ v < m, (((∀ u ∈ hubL v, u < m ∧ ∃ w ∈ hubR u, w = v) ∧ (hubL v).length ≤ p - 1) ∧
      (∀ w ∈ hubR v, w < m ∧ ∃ u ∈ hubL w, u = v)) ∧ (hubR v).length ≤ p - 1 := fun v hv => by
    have := h v hv
    simp only [gH, Bool.and_eq_true, allP_eq, List.all_eq_true, anyL_eq, List.any_eq_true, Nat.beq_eq,
      lenP_eq, Nat.ble_eq, Nat.blt_eq] at this
    exact this
  refine ⟨fun v hv u hu => ?_, fun u hu v hv => ?_, fun v hv => (key v hv).1.1.2, fun u hu => (key u hu).2⟩
  · obtain ⟨h1, w, hw, rfl⟩ := (key v hv).1.1.1 u hu
    exact ⟨h1, hw⟩
  · obtain ⟨h1, x, hx, rfl⟩ := (key u hu).1.2 v hv
    exact ⟨h1, hx⟩


/-! ## The theorem -/

/-- **Main theorem.** Global checks, a certificate at every freed point and the hub graph give a bipartite graph of
maximum degree `p + 2` and diameter at most `7` on `6 (p + 1)(1 + p² + p⁴) + 2m` vertices. -/
theorem main (C : Coder F) (M m : ℕ) (ptc lnA lnB sg sgi rl : ℕ → ℕ) (rflag : ℕ → Bool)
    (cert : ℕ → Cert) (hubL hubR : ℕ → List ℕ)
    (hG : Glob C M ptc lnA lnB sg sgi)
    (hR : ∀ v < m, rl v < M ∧ rflag (rl v) = true)
    (hRs : ∀ v, v + 1 < m → rl v < rl (v + 1))
    (hC : ∀ v < m, CertSpec C (Fintype.card F) M ptc lnA lnB sg rflag (rl v) (cert v))
    (hH1 : ∀ v < m, ∀ u ∈ hubL v, u < m ∧ v ∈ hubR u)
    (hH2 : ∀ u < m, ∀ v ∈ hubR u, v < m ∧ u ∈ hubL v)
    (hH3 : ∀ v < m, (hubL v).length ≤ Fintype.card F - 1) (hH4 : ∀ u < m, (hubR u).length ≤ Fintype.card F - 1)
    (hHL : LocalSpec (Fintype.card F - 1) (2 * m) (hubNb m hubL hubR) (hubCol m))
    (hHB : ∀ s (hs : s < 2 * m) (v : Fin (2 * m)), (graphF (2 * m) (hubNb m hubL hubR)).edist v ⟨s, hs⟩ ≤ 7) :
    ∃ G : SimpleGraph (Fin (6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) + 2 * m)),
      IsBipartiteDegDiam G (Fintype.card F + 2) 7 := by
  letI : Fintype (SPt F) := Fintype.ofFinite _
  letI : Fintype (HLine F) := Fintype.ofFinite _
  have hGP := HexagonEven.genPolygonGraph_hexagon_even (F := F)
  have hcP : Fintype.card (SPt F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_spt_eq]
  have hP : ∀ x : SPt F, (univ.filter (hexInc x)).card = Fintype.card F + 1 := fun x => by
    rw [← card_lns' x, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL : ∀ W : HLine F, (univ.filter (fun x => hexInc x W)).card = Fintype.card F + 1 := fun W => by
    rw [← card_pts' W, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcL : Fintype.card (HLine F) = Fintype.card (SPt F) := by
    have := card_lines_eq (inc := hexInc (F := F)) (k := Fintype.card F + 1) (by omega) (fun x => card_lns' x)
      (fun W => card_pts' W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hgi : ∀ i < M, ∀ j < M, Gl C lnA lnB (sg i) = Gl C lnA lnB (sg j) → i = j := by
    intro i hi j hj h
    have := hG.gl_inj _ (hG.sg i hi).1 _ (hG.sg j hj).1 h
    rw [← (hG.sg i hi).2, ← (hG.sg j hj).2, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_extend hcL.symm (Fp C ptc) (fun i => Gl C lnA lnB (sg i)) hG.fp_inj hgi
  let ownV : Fin m → SPt F := fun v => Fp C ptc (rl v.val)
  have hown : Function.Injective ownV := by
    intro v v' h
    exact Fin.ext (inj_of_succ hRs v.val v.isLt v'.val v'.isLt
      (hG.fp_inj _ (hR v.val v.isLt).1 _ (hR v'.val v'.isLt).1 h))
  have hr2 : ∀ v : Fin m, ∀ y, Coll hexInc (ownV v) y ↔ Conc hexInc (σ (ownV v)) (σ y) := by
    intro v y
    have hir := (hR v.val v.isLt).1
    have hc := hC v.val v.isLt
    have hσr : σ (ownV v) = Gl C lnA lnB (sg (rl v.val)) := hσ _ hir
    rw [coll_iff hG hir hc, hσr, conc_iff hG hir hc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨f, hf, t, ht, hxt⟩ := hc.f4 x hx
      have hxM : x.1 < M := by
        obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        exact ((hc.e2 e he).2.2.2 x hxe).1
      exact ⟨f, hf, t, ht, by rw [hσ _ hxM, hxt]⟩
    · rintro ⟨f, hf, t, ht, hyt⟩
      obtain ⟨x, hx, hxt⟩ := hc.f3 f hf t ht
      have hxM : x.1 < M := by
        obtain ⟨e, he, hxe⟩ := List.mem_flatMap.1 hx
        exact ((hc.e2 e he).2.2.2 x hxe).1
      refine ⟨x, hx, σ.injective ?_⟩
      rw [hyt, hσ _ hxM, hxt]
  have H : Hyp hexInc σ (Set.range ownV) ownV ownV (NSof hubL (m := m)) := {
    pl := pl_of_polygon hGP,
    p2 := p2_of_polygon hGP,
    l2 := l2_of_polygon hGP,
    r1 := by
      rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩ hcoll
      have hir := (hR v.val v.isLt).1
      obtain ⟨x, hx, hxe⟩ := (coll_iff hG hir (hC v.val v.isLt) _).1 hcoll
      obtain ⟨e, he, hxe'⟩ := List.mem_flatMap.1 hx
      obtain ⟨hxM, -, hfl, -⟩ := ((hC v.val v.isLt).e2 e he).2.2.2 x hxe'
      have h1 := hG.fp_inj _ (hR v'.val v'.isLt).1 _ hxM hxe
      have h2 := (hR v'.val v'.isLt).2
      rw [h1, hfl] at h2
      exact Bool.false_ne_true h2,
    r2 := by rintro _ ⟨v, rfl⟩ y; exact hr2 v y,
    ownV_mem := fun v => ⟨v, rfl⟩,
    ownU_mem := fun u => ⟨u, rfl⟩,
    r3V := fun v v' => Or.inr (by
      have := hub_reach' hHL hH2 hHB ⟨v.val, by omega⟩ ⟨v'.val, by omega⟩ (by
        simp only [hubCol]
        rw [show Nat.blt v.val m = true by rw [Nat.blt_eq]; exact v.isLt,
          show Nat.blt v'.val m = true by rw [Nat.blt_eq]; exact v'.isLt])
      rwa [toHub_inl, toHub_inl] at this),
    r3U := fun u u' => Or.inr (by
      have := hub_reach' hHL hH2 hHB ⟨m + u.val, by omega⟩ ⟨m + u'.val, by omega⟩ (by
        simp only [hubCol]
        rw [show Nat.blt (m + u.val) m = false from Bool.eq_false_iff.2 (fun hh => by have := ltOfBlt hh; omega),
          show Nat.blt (m + u'.val) m = false from Bool.eq_false_iff.2 (fun hh => by have := ltOfBlt hh; omega)])
      rwa [toHub_inr, toHub_inr] at this) }
  have hV : ∀ r, (univ.filter (fun v => ownV v = r)).card ≤ 1 := fun r =>
    Finset.card_le_one.2 fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact hown (ha.trans hb.symm)
  have hNV : ∀ v, (univ.filter (NSof hubL v)).card ≤ Fintype.card F - 1 := fun v => by
    convert (card_filter_le_length (m := m) (hubL v.val)).trans (hH3 v.val v.isLt) using 3
    exact Iff.rfl
  have hNU : ∀ u : Fin m, (univ.filter (fun v : Fin m => NSof hubL v u)).card ≤ Fintype.card F - 1 := by
    intro u
    refine le_trans (Finset.card_le_card fun v hv => ?_) ((card_filter_le_length (hubR u.val)).trans
      (hH4 u.val u.isLt))
    have hv' : u.val ∈ hubL v.val := (Finset.mem_filter.1 hv).2
    exact Finset.mem_filter.2 ⟨mem_univ _, (hH1 v.val v.isLt u.val hv').2⟩
  have main := exists_graph (q := Fintype.card F) (j := 1) H (fun x => by convert (hP x).le) (fun W => by convert (hL W).le)
    (fun r => by convert hV r) (fun r => by convert hV r) (fun v => by convert hNV v) (fun u => by convert hNU u)
    Fintype.card_pos
  have e : (2 * 1 + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card (Fin m) +
      Fintype.card (Fin m) = 6 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) + 2 * m := by
    rw [hcL, hcP, Fintype.card_fin]; ring
  rw [e, show Fintype.card F + 1 + 1 = Fintype.card F + 2 by ring] at main
  exact main


/-- `main` with the checks in the form of the generated files. -/
theorem main' (C : Coder F) (q M m K : ℕ) (hq : Fintype.card F = q) (ptc lnA lnB sg sgi rl : ℕ → ℕ) (rflag : ℕ → Bool)
    (cert : ℕ → Cert) (hubL hubR : ℕ → List ℕ)
    (h1 : ∀ i < M, gPt C M ptc i = true) (h2 : ∀ j < M, gLn C M lnA lnB sg sgi j = true)
    (h3 : ∀ v < m, gR M m rl rflag v = true)
    (h4 : ∀ v < m, certOK C q M ptc lnA lnB sg rflag (rl v) (cert v) = true)
    (h5 : ∀ v < m, gH q m hubL hubR v = true)
    (h6 : ∀ u < 2 * m, localOK (q - 1) (2 * m) (hubNb m hubL hubR) (hubCol m) u 1 = true)
    (hK : 2 * m ≤ 2 ^ K) (h7 : bfsOK K 7 (2 * m) 0 (2 * m) (hubNb m hubL hubR) = true) :
    ∃ G : SimpleGraph (Fin (6 * ((q + 1) * (1 + q ^ 2 + q ^ 4)) + 2 * m)), IsBipartiteDegDiam G (q + 2) 7 := by
  subst hq
  obtain ⟨hR, hRs⟩ := r_of h3
  obtain ⟨hH1, hH2, hH3, hH4⟩ := hub_of' h5
  have hHL := localSpec_of h6
  exact main C M m ptc lnA lnB sg sgi rl rflag cert hubL hubR (glob_of h1 h2) hR hRs
    (fun v hv => certSpec_of (h4 v hv)) hH1 hH2 hH3 hH4 hHL
    (fun s hs v => edist_of_bfs' hHL hK h7 v s hs (Nat.zero_le _) (by omega))

end BipartiteDD.LeanAll.HexGen
