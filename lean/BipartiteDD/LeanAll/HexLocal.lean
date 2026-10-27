import BipartiteDD.HexagonD7.Hexagon
import BipartiteDD.LeanAll.HexArith

/-! # Hexagon constructions at diameter 7 from local certificates

Theorem 1 of the hexagon-family project (`HexagonD7.exists_graph`, research/projects/hexagon-family/THEOREM.md) applied
to the split Cayley hexagon `H(p)` over `ZMod p` (Mathlib side: `SPt`, `HLine`, `hexInc`), with three levels (`j = 1`),
a set `R` of freed points, one hub of each kind per point of `R`, and a hub graph. This is the graph of
research/d13D7/multi.c (sol format `multi`). The hypotheses `pl`, `p2`, `l2` of `Hyp` hold in every `H(q)`
(`HexagonEven.genPolygonGraph_hexagon_even`); the others are local to `R`, and `main` reduces them to checks on numbers:

* the domain points `ptc i` (`i < M`, the points of `R` and of every `Γ₂(r)`) and the lines `(lnA j, lnB j)` (`j < M`,
  their images under `σ`), both strictly increasing in their codes, so distinct;
* `sg`: `σ` on the domain (`sgi` its inverse);
* for every `r ∈ R` a certificate (`certOK`): the `p + 1` lines through `r` with the `p` other points of each (domain
  indices), and the `p + 1` points of `σ r` with the `p` other lines through each (line indices), each one checked by
  coordinates (`linN`); the lines of the second list are the images of the points of the first.

Since every line has `p + 1` points and every point is on `p + 1` lines (Mathlib side), these lists are all of
`Γ₂(r)` and `Γ₂(σ r)` (`mem_of_card`), and `σ` is a local duality at `r`. Off the domain `σ` is any bijection
(`exists_equiv_extend`). The hub graph is checked by a search on its `2|R|` vertices (`Orbit2.bfsOK`). -/

namespace BipartiteDD.LeanAll.HexLocal

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open SimpleGraph Finset Module Submodule
open scoped Classical

set_option linter.unusedSectionVars false

/-! ## Lists -/

/-- Strictly increasing, the first entry above `a`. -/
def incFrom : List ℕ → ℕ → Bool :=
  List.rec (fun _ => true) (fun x _ ih a => Nat.blt a x && ih x)

/-- Strictly increasing. -/
def sortedLt : List ℕ → Bool
  | [] => true
  | x :: l => incFrom l x

theorem incFrom_spec : ∀ (l : List ℕ) (a : ℕ), incFrom l a = true → (a :: l).Pairwise (· < ·) := by
  intro l
  induction l with
  | nil => intro a _; simp
  | cons x l ih =>
    intro a h
    simp only [incFrom, Bool.and_eq_true, Nat.blt_eq] at h
    have h2 := ih x h.2
    refine List.Pairwise.cons (fun y hy => ?_) h2
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · exact lt_trans h.1 (List.rel_of_pairwise_cons h2 hy)

theorem sortedLt_spec {l : List ℕ} (h : sortedLt l = true) : l.Pairwise (· < ·) := by
  cases l with
  | nil => simp
  | cons x l => exact incFrom_spec l x h

theorem nodup_of_sortedLt {l : List ℕ} (h : sortedLt l = true) : l.Nodup :=
  (sortedLt_spec h).imp (fun h => ne_of_lt h)

theorem nodup_map_of {α β γ : Type*} {l : List α} {g : α → β} {h : α → γ} (hh : (l.map h).Nodup)
    (hgh : ∀ x ∈ l, ∀ y ∈ l, g x = g y → h x = h y) : (l.map g).Nodup := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hh ⊢
    refine ⟨fun ⟨y, hy, hxy⟩ => hh.1 ⟨y, hy, (hgh x (List.mem_cons_self ..) y (List.mem_cons_of_mem _ hy)
      hxy.symm).symm⟩, ih hh.2 (fun a ha b hb => hgh a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))⟩

/-- `List.all` by `List.rec`. -/
def allP {α : Type} (f : α → Bool) (l : List α) : Bool := List.rec true (fun x _ ih => f x && ih) l

theorem allP_eq {α : Type} (f : α → Bool) (l : List α) : allP f l = l.all f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [allP, List.all_cons] at ih ⊢; rw [ih]

/-- `List.length` by `List.rec`. -/
def lenP {α : Type} (l : List α) : ℕ := List.rec 0 (fun _ _ ih => Nat.succ ih) l

theorem lenP_eq {α : Type} (l : List α) : lenP l = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [lenP, List.length_cons] at ih ⊢; rw [ih]

/-- Or of `f` over a list, by `List.rec`. -/
def orP {α : Type} (f : α → ℕ) (l : List α) : ℕ := List.rec 0 (fun x _ ih => Nat.lor (f x) ih) l

theorem testBit_orP {α : Type} (f : α → ℕ) (l : List α) (j : ℕ) :
    (orP f l).testBit j = true → ∃ x ∈ l, (f x).testBit j = true := by
  induction l with
  | nil => intro h; simp [orP] at h
  | cons x l ih =>
    intro h
    have h' : (f x ||| orP f l).testBit j = true := h
    rw [Nat.testBit_lor] at h'
    rcases Bool.or_eq_true_iff.1 h' with h1 | h1
    · exact ⟨x, List.mem_cons_self .., h1⟩
    · obtain ⟨y, hy, h2⟩ := ih h1
      exact ⟨y, List.mem_cons_of_mem _ hy, h2⟩

/-! ## Points and lines of `H(p)` from numbers -/

variable {p : ℕ} [hp : Fact p.Prime]

/-- A point code: below `p⁷`, normalised, on the quadric. -/
structure PtOK (p : ℕ) [Fact p.Prime] (c : ℕ) : Prop where
  lt : c < p ^ 7
  nrm : Nrm (vec p c)
  q : Qf (vec p c) = 0

/-- The check for `PtOK`. -/
def ptOKb (p c : ℕ) : Bool := Nat.blt c (Nat.pow p 7) && firstOne (cd p c) 0 7 && qN p c

theorem ptOKb_spec {c : ℕ} (h : ptOKb p c = true) : PtOK p c := by
  simp only [ptOKb, Bool.and_eq_true, Nat.blt_eq] at h
  exact ⟨h.1.1, nrm_vec h.1.2, qN_spec h.2⟩

/-- A line basis: a pair of the hexagon with normalised Plücker coordinates. -/
structure LnOK (p : ℕ) [Fact p.Prime] (a b : ℕ) : Prop where
  pair : IsHPair (vec p a) (vec p b)
  nrm : Nrm (plV (vec p a) (vec p b))

/-- The check for `LnOK`. -/
def lnOKb (p a b : ℕ) : Bool := qN p a && qN p b && bN p a b && tN p a b && firstOneL (plL p a b)

theorem lnOKb_spec {a b : ℕ} (h : lnOKb p a b = true) : LnOK p a b := by
  simp only [lnOKb, Bool.and_eq_true] at h
  exact ⟨⟨qN_spec h.1.1.1.1, qN_spec h.1.1.1.2, bN_spec h.1.1.2, tN_spec h.1.2⟩, nrm_plV h.2⟩

theorem plV_smul_right {K : Type*} [Field K] (x : V7 K) (t : K) : plV x (t • x) = 0 := by
  funext k; simp only [plV, pl, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]; ring

theorem plV_zero_left {K : Type*} [Field K] (y : V7 K) : plV 0 y = 0 := by
  funext k; simp only [plV, pl, Pi.zero_apply, zero_mul, sub_self]

theorem LnOK.ne_zero {a b : ℕ} (h : LnOK p a b) : vec p a ≠ 0 := by
  intro h0
  have := h.nrm.ne_zero
  rw [h0, plV_zero_left] at this
  exact this rfl

theorem LnOK.not_mem {a b : ℕ} (h : LnOK p a b) : vec p b ∉ span (ZMod p) {vec p a} := by
  intro hm
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hm
  have := h.nrm.ne_zero
  rw [← ht, plV_smul_right] at this
  exact this rfl

theorem qf_rep {v : V7 (ZMod p)} (hv : v ≠ 0) (hq : Qf v = 0) :
    Qf (Projectivization.mk (ZMod p) v hv).rep = 0 := by
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff (ZMod p) _ v
    (Projectivization.mk (ZMod p) v hv).rep_nonzero hv).1 (Projectivization.mk_rep _)
  rw [← ha, Units.smul_def, Qf_smul, hq, mul_zero]

instance : Nonempty (SPt (ZMod p)) := by
  have h : Nat.card (SPt (ZMod p)) ≠ 0 := by
    rw [card_spt_eq]; positivity
  exact (Nat.card_ne_zero.1 h).1

instance : Finite (SPt (ZMod p)) := Finite.of_injective (fun x : SPt (ZMod p) => x.1) Subtype.val_injective

instance : Finite (HLine (ZMod p)) := HexagonEven.finite_hline_even

instance : Nonempty (HLine (ZMod p)) := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (SPt (ZMod p)))
  have h : Nat.card {W : HLine (ZMod p) // x.1.rep ∈ W.1} ≠ 0 := by
    rw [HexagonEven.card_lines_through_even]; omega
  obtain ⟨⟨W, -⟩⟩ := (Nat.card_ne_zero.1 h).1
  exact ⟨W⟩

/-- The point of a code (a fixed point if the code is not valid). -/
noncomputable def ptOf (p : ℕ) [Fact p.Prime] (c : ℕ) : SPt (ZMod p) :=
  if h : PtOK p c then ⟨Projectivization.mk _ (vec p c) h.nrm.ne_zero, qf_rep _ h.q⟩
  else Classical.arbitrary _

/-- The line of a basis (a fixed line if it is not valid). -/
noncomputable def lineOf (p : ℕ) [Fact p.Prime] (a b : ℕ) : HLine (ZMod p) :=
  if h : LnOK p a b then hlineOf h.ne_zero h.pair h.not_mem else Classical.arbitrary _

theorem lineOf_val {a b : ℕ} (h : LnOK p a b) : (lineOf p a b).1 = span (ZMod p) {vec p a, vec p b} := by
  rw [lineOf, dif_pos h]; rfl

theorem ptOf_rep_mem {c : ℕ} (h : PtOK p c) (W : Submodule (ZMod p) (V7 (ZMod p))) :
    (ptOf p c).1.rep ∈ W ↔ vec p c ∈ W := by
  simp only [ptOf, dif_pos h]
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff (ZMod p) _ (vec p c)
    (Projectivization.mk (ZMod p) (vec p c) h.nrm.ne_zero).rep_nonzero h.nrm.ne_zero).1
    (Projectivization.mk_rep _)
  rw [← ha]
  exact Submodule.smul_mem_iff_of_isUnit W a.isUnit

/-- Incidence from coordinates. -/
theorem inc_of_lin {y a b α β : ℕ} (hy : PtOK p y) (hl : LnOK p a b) (h : linN p y a b α β = true) :
    hexInc (ptOf p y) (lineOf p a b) := by
  show (ptOf p y).1.rep ∈ (lineOf p a b).1
  rw [ptOf_rep_mem hy, lineOf_val hl, linN_spec h]
  exact Submodule.mem_span_pair.2 ⟨α, β, rfl⟩

/-- The first basis vector is on the line. -/
theorem inc_first {y b : ℕ} (hy : PtOK p y) (hl : LnOK p y b) : hexInc (ptOf p y) (lineOf p y b) := by
  show (ptOf p y).1.rep ∈ (lineOf p y b).1
  rw [ptOf_rep_mem hy, lineOf_val hl]
  exact subset_span (by simp)

theorem ptOf_inj {c c' : ℕ} (h : PtOK p c) (h' : PtOK p c') (he : ptOf p c = ptOf p c') : c = c' := by
  simp only [ptOf, dif_pos h, dif_pos h', Subtype.mk.injEq] at he
  obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff (ZMod p) _ _ h.nrm.ne_zero h'.nrm.ne_zero).1 he
  have : vec p c = vec p c' := Nrm.eq_of_smul h'.nrm h.nrm (a := (a : ZMod p)) (by rw [← ha, Units.smul_def])
  exact eq_of_vec h.lt h'.lt this

theorem lineOf_inj {a b a' b' : ℕ} (h : LnOK p a b) (h' : LnOK p a' b') (he : lineOf p a b = lineOf p a' b') :
    plCode p a b = plCode p a' b' := by
  have hs := congrArg Subtype.val he
  rw [lineOf_val h, lineOf_val h'] at hs
  have ha' : vec p a' ∈ span (ZMod p) {vec p a, vec p b} := by rw [hs]; exact subset_span (by simp)
  have hb' : vec p b' ∈ span (ZMod p) {vec p a, vec p b} := by rw [hs]; exact subset_span (by simp)
  obtain ⟨s, t, hst⟩ := Submodule.mem_span_pair.1 ha'
  obtain ⟨u, w, huw⟩ := Submodule.mem_span_pair.1 hb'
  have hpl : plV (vec p a') (vec p b') = (s * w - t * u) • plV (vec p a) (vec p b) := by
    rw [← hst, ← huw, plV_comb]
  have := Nrm.eq_of_smul h.nrm h'.nrm hpl
  unfold plCode
  rw [plL_eq_of_plV this.symm]

/-! ## Counting -/

/-- `k` distinct elements with a property that exactly `k` elements have are all of them. -/
theorem mem_of_card {α : Type*} [Finite α] {S : α → Prop} {k : ℕ} (hS : Nat.card {x // S x} = k) (l : List α)
    (hl : l.length = k) (hnd : l.Nodup) (hin : ∀ x ∈ l, S x) : ∀ x, S x → x ∈ l := by
  haveI := Fintype.ofFinite α
  intro x hx
  have hT : (univ.filter S).card = k := by rw [← hS, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : l.toFinset ⊆ univ.filter S := fun y hy => by
    simp only [mem_filter, mem_univ, true_and]; exact hin y (List.mem_toFinset.1 hy)
  have hc : (univ.filter S).card ≤ l.toFinset.card := by
    rw [hT, List.toFinset_card_of_nodup hnd, hl]
  have heq := Finset.eq_of_subset_of_card_le hsub hc
  have : x ∈ univ.filter S := by simp [hx]
  rw [← heq] at this
  exact List.mem_toFinset.1 this

theorem card_pts (W : HLine (ZMod p)) : Nat.card {x : SPt (ZMod p) // hexInc x W} = p + 1 := by
  have := card_points_hline W
  rw [ZMod.card] at this
  exact this

theorem card_lns (x : SPt (ZMod p)) : Nat.card {W : HLine (ZMod p) // hexInc x W} = p + 1 := by
  have := HexagonEven.card_lines_through_even x
  rw [ZMod.card] at this
  exact this

/-! ## Extending an injection to a bijection -/

theorem exists_equiv_extend {P L : Type*} [Fintype P] [Fintype L] (hc : Fintype.card P = Fintype.card L)
    {M : ℕ} (f : ℕ → P) (g : ℕ → L) (hf : ∀ i < M, ∀ j < M, f i = f j → i = j)
    (hg : ∀ i < M, ∀ j < M, g i = g j → i = j) : ∃ σ : P ≃ L, ∀ i < M, σ (f i) = g i := by
  let f' : Fin M → P := fun i => f i
  let g' : Fin M → L := fun i => g i
  have hf' : Function.Injective f' := fun i j h => Fin.ext (hf i i.isLt j j.isLt h)
  have hg' : Function.Injective g' := fun i j h => Fin.ext (hg i i.isLt j j.isLt h)
  let e0 : Set.range f' ≃ Set.range g' := (Equiv.ofInjective f' hf').symm.trans (Equiv.ofInjective g' hg')
  have hcard : Fintype.card {x // x ∉ Set.range f'} = Fintype.card {y // y ∉ Set.range g'} := by
    have h1 : Fintype.card {x // x ∈ Set.range f'} = Fintype.card (Fin M) := Set.card_range_of_injective hf'
    have h2 : Fintype.card {y // y ∈ Set.range g'} = Fintype.card (Fin M) := Set.card_range_of_injective hg'
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, h1, h2, hc]
  let e1 : {x // x ∉ Set.range f'} ≃ {y // y ∉ Set.range g'} := Fintype.equivOfCardEq hcard
  let σ : P ≃ L := ((Equiv.sumCompl (fun x => x ∈ Set.range f')).symm.trans (Equiv.sumCongr e0 e1)).trans
    (Equiv.sumCompl (fun y => y ∈ Set.range g'))
  refine ⟨σ, fun i hi => ?_⟩
  have hm : f i ∈ Set.range f' := ⟨⟨i, hi⟩, rfl⟩
  simp only [σ, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_pos hm, Equiv.sumCongr_apply, Sum.map_inl,
    Equiv.sumCompl_apply_inl, e0]
  have : (Equiv.ofInjective f' hf').symm ⟨f i, hm⟩ = ⟨i, hi⟩ := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]
  rfl

/-! ## The certificate of one freed point -/

/-- Lines through `r` (an extra vector and the other points: index, `α`, `β`), and points of `σ r` (code, `α`, `β`,
and the other lines: index, `γ`, `δ`, position in the first list). -/
abbrev Cert := List (ℕ × List (ℕ × ℕ × ℕ)) × List ((ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ))

/-- The positions `e` of the second list cover `0 … k-1`. -/
def maskOf (fs : List ((ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ))) : ℕ :=
  orP (fun f => orP (fun t => Nat.shiftLeft 1 t.2.2.2) f.2) fs

/-- The check of a certificate at the domain point `ir` (`L0 = sg ir`). -/
def certOK (p M : ℕ) (ptc lnA lnB sg : ℕ → ℕ) (rflag : ℕ → Bool) (ir : ℕ) (c : Cert) : Bool :=
  Nat.beq (lenP c.1) (p + 1) &&
  sortedLt (c.1.map (fun e => plCode p (ptc ir) e.1)) &&
  allP (fun e => lnOKb p (ptc ir) e.1 && Nat.beq (lenP e.2) p && sortedLt (e.2.map (·.1)) &&
    allP (fun t => Nat.blt t.1 M && !(Nat.beq t.1 ir) && !(rflag t.1) &&
      linN p (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2) e.2) c.1 &&
  Nat.beq (lenP c.2) (p + 1) &&
  sortedLt (c.2.map (·.1.1)) &&
  allP (fun f => ptOKb p f.1.1 && linN p f.1.1 (lnA (sg ir)) (lnB (sg ir)) f.1.2.1 f.1.2.2 &&
    Nat.beq (lenP f.2) p && sortedLt (f.2.map (·.1)) &&
    allP (fun t => Nat.blt t.1 M && !(Nat.beq t.1 (sg ir)) &&
      linN p f.1.1 (lnA t.1) (lnB t.1) t.2.1 t.2.2.1 && Nat.blt t.2.2.2 (p * (p + 1)) &&
      Nat.beq (sg ((c.1.flatMap (·.2)).getD t.2.2.2 (0, 0, 0)).1) t.1) f.2) c.2 &&
  Nat.beq (maskOf c.2) (2 ^ (p * (p + 1)) - 1)

/-- What a passing `certOK` says. -/
structure CertSpec (p M : ℕ) [Fact p.Prime] (ptc lnA lnB sg : ℕ → ℕ) (rflag : ℕ → Bool) (ir : ℕ) (c : Cert) : Prop where
  e0 : c.1.length = p + 1
  e1 : (c.1.map (fun e => plCode p (ptc ir) e.1)).Nodup
  e2 : ∀ e ∈ c.1, LnOK p (ptc ir) e.1 ∧ e.2.length = p ∧ (e.2.map (·.1)).Nodup ∧
    ∀ t ∈ e.2, t.1 < M ∧ t.1 ≠ ir ∧ rflag t.1 = false ∧ linN p (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2 = true
  f0 : c.2.length = p + 1
  f1 : (c.2.map (·.1.1)).Nodup
  f2 : ∀ f ∈ c.2, PtOK p f.1.1 ∧ linN p f.1.1 (lnA (sg ir)) (lnB (sg ir)) f.1.2.1 f.1.2.2 = true ∧
    f.2.length = p ∧ (f.2.map (·.1)).Nodup ∧
    ∀ t ∈ f.2, t.1 < M ∧ t.1 ≠ sg ir ∧ linN p f.1.1 (lnA t.1) (lnB t.1) t.2.1 t.2.2.1 = true
  f3 : ∀ f ∈ c.2, ∀ t ∈ f.2, ∃ x ∈ c.1.flatMap (·.2), sg x.1 = t.1
  f4 : ∀ x ∈ c.1.flatMap (·.2), ∃ f ∈ c.2, ∃ t ∈ f.2, sg x.1 = t.1

theorem mem_of_mask {fs : List ((ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ × ℕ))} {k : ℕ} (h : maskOf fs = 2 ^ k - 1)
    (j : ℕ) (hj : j < k) : ∃ f ∈ fs, ∃ t ∈ f.2, t.2.2.2 = j := by
  have hb : (maskOf fs).testBit j = true := by rw [h, Nat.testBit_two_pow_sub_one]; simpa using hj
  obtain ⟨f, hf, h1⟩ := testBit_orP _ _ _ hb
  obtain ⟨t, ht, h2⟩ := testBit_orP _ _ _ h1
  refine ⟨f, hf, t, ht, ?_⟩
  change (1 <<< t.2.2.2).testBit j = true at h2
  rw [Nat.shiftLeft_eq, one_mul, Nat.testBit_two_pow] at h2
  exact of_decide_eq_true h2

theorem length_flatMap {es : List (ℕ × List (ℕ × ℕ × ℕ))} {k : ℕ} (h : ∀ e ∈ es, e.2.length = k) :
    (es.flatMap (·.2)).length = es.length * k := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    rw [h e (List.mem_cons_self ..), ih (fun e' he' => h e' (List.mem_cons_of_mem _ he'))]
    ring

theorem certSpec_of {M : ℕ} {ptc lnA lnB sg : ℕ → ℕ} {rflag : ℕ → Bool} {ir : ℕ} {c : Cert}
    (h : certOK p M ptc lnA lnB sg rflag ir c = true) : CertSpec p M ptc lnA lnB sg rflag ir c := by
  simp only [certOK, Bool.and_eq_true, Nat.beq_eq, allP_eq, lenP_eq, List.all_eq_true, Nat.blt_eq,
    Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hE0, hE1⟩, hE2⟩, hF0⟩, hF1⟩, hF2⟩, hM⟩ := h
  have hE2' : ∀ e ∈ c.1, LnOK p (ptc ir) e.1 ∧ e.2.length = p ∧ (e.2.map (·.1)).Nodup ∧
      ∀ t ∈ e.2, t.1 < M ∧ t.1 ≠ ir ∧ rflag t.1 = false ∧ linN p (ptc t.1) (ptc ir) e.1 t.2.1 t.2.2 = true := by
    intro e he
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hE2 e he
    exact ⟨lnOKb_spec h1, h2, nodup_of_sortedLt h3, fun t ht => by
      obtain ⟨⟨⟨h5, h6⟩, h7⟩, h8⟩ := h4 t ht
      exact ⟨h5, fun h => by simp [h] at h6, by simpa using h7, h8⟩⟩
  have hlen : (c.1.flatMap (·.2)).length = p * (p + 1) := by
    rw [length_flatMap (k := p) (fun e he => (hE2' e he).2.1), hE0]; ring
  refine ⟨hE0, nodup_of_sortedLt hE1, hE2', hF0, nodup_of_sortedLt hF1, fun f hf => ?_, fun f hf t ht => ?_,
    fun x hx => ?_⟩
  · obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hF2 f hf
    exact ⟨ptOKb_spec h1, h2, h3, nodup_of_sortedLt h4, fun t ht => by
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
noncomputable def Fp (p : ℕ) [Fact p.Prime] (ptc : ℕ → ℕ) (i : ℕ) : SPt (ZMod p) := ptOf p (ptc i)

/-- The domain lines. -/
noncomputable def Gl (p : ℕ) [Fact p.Prime] (lnA lnB : ℕ → ℕ) (j : ℕ) : HLine (ZMod p) := lineOf p (lnA j) (lnB j)

/-- The global checks. -/
structure Glob (p M : ℕ) [Fact p.Prime] (ptc lnA lnB sg sgi : ℕ → ℕ) : Prop where
  pt : ∀ i < M, PtOK p (ptc i)
  ptinc : ∀ i, i + 1 < M → ptc i < ptc (i + 1)
  ln : ∀ j < M, LnOK p (lnA j) (lnB j)
  lninc : ∀ j, j + 1 < M → plCode p (lnA j) (lnB j) < plCode p (lnA (j + 1)) (lnB (j + 1))
  sg : ∀ i < M, sg i < M ∧ sgi (sg i) = i

theorem strictMono_of_succ {f : ℕ → ℕ} {M : ℕ} (h : ∀ i, i + 1 < M → f i < f (i + 1)) :
    ∀ i j, i < j → j < M → f i < f j := by
  intro i j hij hj
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h1 | h1
    · exact lt_trans (ih h1 (by omega)) (h j hj)
    · rw [h1]; exact h j hj

theorem inj_of_succ {f : ℕ → ℕ} {M : ℕ} (h : ∀ i, i + 1 < M → f i < f (i + 1)) :
    ∀ i < M, ∀ j < M, f i = f j → i = j := by
  intro i hi j hj he
  rcases lt_trichotomy i j with h1 | h1 | h1
  · exact absurd he (ne_of_lt (strictMono_of_succ h i j h1 hj))
  · exact h1
  · exact absurd he.symm (ne_of_lt (strictMono_of_succ h j i h1 hi))

variable {sgi : ℕ → ℕ}

theorem Glob.fp_inj (hG : Glob p M ptc lnA lnB sg sgi) : ∀ i < M, ∀ j < M, Fp p ptc i = Fp p ptc j → i = j :=
  fun i hi j hj he => inj_of_succ hG.ptinc i hi j hj (ptOf_inj (hG.pt i hi) (hG.pt j hj) he)

theorem Glob.gl_inj (hG : Glob p M ptc lnA lnB sg sgi) : ∀ i < M, ∀ j < M, Gl p lnA lnB i = Gl p lnA lnB j → i = j :=
  fun i hi j hj he => inj_of_succ (f := fun j => plCode p (lnA j) (lnB j)) hG.lninc i hi j hj
    (lineOf_inj (hG.ln i hi) (hG.ln j hj) he)

/-- The points collinear with a freed point are the first list of its certificate. -/
theorem coll_iff (hG : Glob p M ptc lnA lnB sg sgi) {ir : ℕ} (hir : ir < M) {c : Cert}
    (hc : CertSpec p M ptc lnA lnB sg rflag ir c) (y : SPt (ZMod p)) :
    Coll hexInc (Fp p ptc ir) y ↔ ∃ x ∈ c.1.flatMap (·.2), y = Fp p ptc x.1 := by
  have hr := hG.pt ir hir
  constructor
  · rintro ⟨hne, W, hrW, hyW⟩
    have hW : W ∈ c.1.map (fun e => lineOf p (ptc ir) e.1) := by
      refine mem_of_card (card_lns (Fp p ptc ir)) _ (by rw [List.length_map, hc.e0]) ?_ ?_ W hrW
      · exact nodup_map_of hc.e1 (fun e he e' he' hee => lineOf_inj (hc.e2 e he).1 (hc.e2 e' he').1 hee)
      · intro W' hW'
        obtain ⟨e, he, rfl⟩ := List.mem_map.1 hW'
        exact inc_first hr (hc.e2 e he).1
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hW
    obtain ⟨hl, hlen, hnd, hent⟩ := hc.e2 e he
    have hy : y ∈ Fp p ptc ir :: e.2.map (fun t => Fp p ptc t.1) := by
      refine mem_of_card (card_pts _) _ (by simp [hlen]) ?_ ?_ y hyW
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
    refine ⟨fun h => (hent x ht).2.1 (hG.fp_inj _ (hent x ht).1 _ hir h.symm), lineOf p (ptc ir) e.1,
      inc_first hr hl, inc_of_lin (hG.pt _ (hent x ht).1) hl (hent x ht).2.2.2⟩

/-- The lines concurrent with `σ r` are the second list of the certificate. -/
theorem conc_iff (hG : Glob p M ptc lnA lnB sg sgi) {ir : ℕ} (hir : ir < M) {c : Cert}
    (hc : CertSpec p M ptc lnA lnB sg rflag ir c) (W : HLine (ZMod p)) :
    Conc hexInc (Gl p lnA lnB (sg ir)) W ↔ ∃ f ∈ c.2, ∃ t ∈ f.2, W = Gl p lnA lnB t.1 := by
  have hL0 := (hG.sg ir hir).1
  have hl := hG.ln _ hL0
  constructor
  · rintro ⟨hne, x, hxl, hxW⟩
    have hx : x ∈ c.2.map (fun f => ptOf p f.1.1) := by
      refine mem_of_card (card_pts _) _ (by rw [List.length_map, hc.f0]) ?_ ?_ x hxl
      · exact nodup_map_of hc.f1 (fun f hf f' hf' hff => ptOf_inj (hc.f2 f hf).1 (hc.f2 f' hf').1 hff)
      · intro x' hx'
        obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx'
        exact inc_of_lin (hc.f2 f hf).1 hl (hc.f2 f hf).2.1
    obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hx
    obtain ⟨hz, hzl, hlen, hnd, hent⟩ := hc.f2 f hf
    have hW : W ∈ Gl p lnA lnB (sg ir) :: f.2.map (fun t => Gl p lnA lnB t.1) := by
      refine mem_of_card (card_lns _) _ (by simp [hlen]) ?_ ?_ W hxW
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
    exact ⟨fun h => (hent t ht).2.1 (hG.gl_inj _ (hent t ht).1 _ hL0 h.symm), ptOf p f.1.1,
      inc_of_lin hz hl hzl, inc_of_lin hz (hG.ln _ (hent t ht).1) (hent t ht).2.2⟩

end Gamma


/-! ## The hub graph -/

theorem ltOfBlt {a b : ℕ} (h : Nat.blt a b = true) : a < b := by rw [Nat.blt_eq] at h; exact h

/-- Neighbour lists of the hub graph on `2m` vertices: hub `v` of the first kind is `v`, hub `u` of the second kind
is `m + u`. -/
def hubNb (m : ℕ) (hubL hubR : ℕ → List ℕ) (w : ℕ) : List ℕ :=
  cond (Nat.blt w m) ((hubL w).map (fun u => Nat.add m u)) (hubR (Nat.sub w m))

/-- Its colouring. -/
def hubCol (m w : ℕ) : Bool := Nat.blt w m

theorem col_walk {d n : ℕ} {nb : ℕ → List ℕ} {c : ℕ → Bool} (hL : LocalSpec d n nb c) {a b : Fin n}
    (w : (graphF n nb).Walk a b) : (c a.val = c b.val ↔ Even w.length) := by
  induction w with
  | nil => simp
  | @cons a x b h w ih =>
    have hc := hL.col a.val a.isLt x.val ((adj_iff hL).1 h)
    rw [Walk.length_cons, Nat.even_add_one, ← ih]
    cases h1 : c a.val <;> cases h2 : c x.val <;> cases h3 : c b.val <;> simp_all

/-- The hub graph of the lists. -/
def NSof (hubL : ℕ → List ℕ) {m : ℕ} (v u : Fin m) : Prop := u.val ∈ hubL v.val

/-- Vertices of the search graph as hubs. -/
def toHub (m : ℕ) (w : Fin (2 * m)) : Fin m ⊕ Fin m :=
  if h : w.val < m then .inl ⟨w.val, h⟩ else .inr ⟨w.val - m, by have := w.isLt; omega⟩

theorem toHub_inl {m : ℕ} (v : Fin m) : toHub m ⟨v.val, by omega⟩ = .inl v := by
  simp [toHub, v.isLt]

theorem toHub_inr {m : ℕ} (u : Fin m) : toHub m ⟨m + u.val, by omega⟩ = .inr u := by
  simp [toHub]

/-- The search graph maps onto the hub graph. -/
def hubHom {m : ℕ} {hubL hubR : ℕ → List ℕ} (hHL : LocalSpec (p - 1) (2 * m) (hubNb m hubL hubR) (hubCol m))
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

theorem hub_reach {m : ℕ} {hubL hubR : ℕ → List ℕ}
    (hHL : LocalSpec (p - 1) (2 * m) (hubNb m hubL hubR) (hubCol m))
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
  exact Reach.map (hubHom hHL hH2) h6

/-! ## The theorem -/

theorem card_filter_le_length {m : ℕ} (l : List ℕ) :
    (univ.filter (fun u : Fin m => u.val ∈ l)).card ≤ l.length := by
  refine le_trans ?_ (List.toFinset_card_le l)
  refine Finset.card_le_card_of_injOn (fun u => u.val) (fun u hu => ?_) (fun u _ w _ h => Fin.ext h)
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu
  exact List.mem_toFinset.2 hu

/-- **Main theorem.** Global checks, a certificate at every freed point and the hub graph give a bipartite graph of
maximum degree `p + 2` and diameter at most `7` on `6 (p + 1)(1 + p² + p⁴) + 2m` vertices. -/
theorem main (p : ℕ) [Fact p.Prime] (M m : ℕ) (ptc lnA lnB sg sgi rl : ℕ → ℕ) (rflag : ℕ → Bool)
    (cert : ℕ → Cert) (hubL hubR : ℕ → List ℕ)
    (hG : Glob p M ptc lnA lnB sg sgi)
    (hR : ∀ v < m, rl v < M ∧ rflag (rl v) = true)
    (hRs : ∀ v, v + 1 < m → rl v < rl (v + 1))
    (hC : ∀ v < m, CertSpec p M ptc lnA lnB sg rflag (rl v) (cert v))
    (hH1 : ∀ v < m, ∀ u ∈ hubL v, u < m ∧ v ∈ hubR u)
    (hH2 : ∀ u < m, ∀ v ∈ hubR u, v < m ∧ u ∈ hubL v)
    (hH3 : ∀ v < m, (hubL v).length ≤ p - 1) (hH4 : ∀ u < m, (hubR u).length ≤ p - 1)
    (hHL : LocalSpec (p - 1) (2 * m) (hubNb m hubL hubR) (hubCol m))
    (hHB : ∀ s (hs : s < 2 * m) (v : Fin (2 * m)), (graphF (2 * m) (hubNb m hubL hubR)).edist v ⟨s, hs⟩ ≤ 7) :
    ∃ G : SimpleGraph (Fin (6 * ((p + 1) * (1 + p ^ 2 + p ^ 4)) + 2 * m)), IsBipartiteDegDiam G (p + 2) 7 := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  have hGP := HexagonEven.genPolygonGraph_hexagon_even (F := ZMod p)
  have hcP : Fintype.card (SPt (ZMod p)) = (p + 1) * (1 + p ^ 2 + p ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_spt_eq, ZMod.card]
  have hP : ∀ x : SPt (ZMod p), (univ.filter (hexInc x)).card = p + 1 := fun x => by
    rw [← card_lns x, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hL : ∀ W : HLine (ZMod p), (univ.filter (fun x => hexInc x W)).card = p + 1 := fun W => by
    rw [← card_pts W, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hcL : Fintype.card (HLine (ZMod p)) = Fintype.card (SPt (ZMod p)) := by
    have := card_lines_eq (inc := hexInc (F := ZMod p)) (k := p + 1) (by omega) (fun x => card_lns x)
      (fun W => card_pts W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hgi : ∀ i < M, ∀ j < M, Gl p lnA lnB (sg i) = Gl p lnA lnB (sg j) → i = j := by
    intro i hi j hj h
    have := hG.gl_inj _ (hG.sg i hi).1 _ (hG.sg j hj).1 h
    rw [← (hG.sg i hi).2, ← (hG.sg j hj).2, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_extend hcL.symm (Fp p ptc) (fun i => Gl p lnA lnB (sg i)) hG.fp_inj hgi
  let ownV : Fin m → SPt (ZMod p) := fun v => Fp p ptc (rl v.val)
  have hown : Function.Injective ownV := by
    intro v v' h
    exact Fin.ext (inj_of_succ hRs v.val v.isLt v'.val v'.isLt
      (hG.fp_inj _ (hR v.val v.isLt).1 _ (hR v'.val v'.isLt).1 h))
  have hr2 : ∀ v : Fin m, ∀ y, Coll hexInc (ownV v) y ↔ Conc hexInc (σ (ownV v)) (σ y) := by
    intro v y
    have hir := (hR v.val v.isLt).1
    have hc := hC v.val v.isLt
    have hσr : σ (ownV v) = Gl p lnA lnB (sg (rl v.val)) := hσ _ hir
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
      have := hub_reach hHL hH2 hHB ⟨v.val, by omega⟩ ⟨v'.val, by omega⟩ (by
        simp only [hubCol]
        rw [show Nat.blt v.val m = true by rw [Nat.blt_eq]; exact v.isLt,
          show Nat.blt v'.val m = true by rw [Nat.blt_eq]; exact v'.isLt])
      rwa [toHub_inl, toHub_inl] at this),
    r3U := fun u u' => Or.inr (by
      have := hub_reach hHL hH2 hHB ⟨m + u.val, by omega⟩ ⟨m + u'.val, by omega⟩ (by
        simp only [hubCol]
        rw [show Nat.blt (m + u.val) m = false from Bool.eq_false_iff.2 (fun hh => by have := ltOfBlt hh; omega),
          show Nat.blt (m + u'.val) m = false from Bool.eq_false_iff.2 (fun hh => by have := ltOfBlt hh; omega)])
      rwa [toHub_inr, toHub_inr] at this) }
  have hV : ∀ r, (univ.filter (fun v => ownV v = r)).card ≤ 1 := fun r =>
    Finset.card_le_one.2 fun a ha b hb => by
      simp only [mem_filter, mem_univ, true_and] at ha hb
      exact hown (ha.trans hb.symm)
  have hNV : ∀ v, (univ.filter (NSof hubL v)).card ≤ p - 1 := fun v => by
    convert (card_filter_le_length (m := m) (hubL v.val)).trans (hH3 v.val v.isLt) using 3
    exact Iff.rfl
  have hNU : ∀ u : Fin m, (univ.filter (fun v : Fin m => NSof hubL v u)).card ≤ p - 1 := by
    intro u
    refine le_trans (Finset.card_le_card fun v hv => ?_) ((card_filter_le_length (hubR u.val)).trans
      (hH4 u.val u.isLt))
    have hv' : u.val ∈ hubL v.val := (Finset.mem_filter.1 hv).2
    exact Finset.mem_filter.2 ⟨mem_univ _, (hH1 v.val v.isLt u.val hv').2⟩
  have main := exists_graph (q := p) (j := 1) H (fun x => by convert (hP x).le) (fun W => by convert (hL W).le)
    (fun r => by convert hV r) (fun r => by convert hV r) (fun v => by convert hNV v) (fun u => by convert hNU u)
    (Nat.Prime.one_lt (Fact.out)).le
  have e : (2 * 1 + 1) * (Fintype.card (SPt (ZMod p)) + Fintype.card (HLine (ZMod p))) + Fintype.card (Fin m) +
      Fintype.card (Fin m) = 6 * ((p + 1) * (1 + p ^ 2 + p ^ 4)) + 2 * m := by
    rw [hcL, hcP, Fintype.card_fin]; ring
  rw [e, show p + 1 + 1 = p + 2 by ring] at main
  exact main

end BipartiteDD.LeanAll.HexLocal
