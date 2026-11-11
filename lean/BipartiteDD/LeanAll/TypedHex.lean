import BipartiteDD.LeanAll.Typed
import BipartiteDD.LeanAll.HexLocal

/-! # Typed levels over `H(p)`: certificates

Tools for instances of `Typed.THyp` over the split Cayley hexagon `H(p)` (`ZMod p`, Mathlib side), with the elements
`SPt ⊕ HLine`:

* `base_hex`: the walk facts of `H(p)`;
* `co_inl`, `co_inr`: co-adjacency is collinearity of points and concurrency of lines;
* `swapE τ`: the bijection `p ↦ τ p`, `l ↦ τ⁻¹ l` of the elements, for the transitions `H → H` (points to lines by
  `τ`) and `H^D → H^D` (lines to points by `τ⁻¹`);
* friendly freed sets: `rhOK`/`rh_noncoll` (points, with the lines through each of them in a global table that is
  strictly increasing in the line code, each line tagged with its point) and `rlOK`/`rl_noncon` (lines, dually);
* `local_duality`: a `HexLocal` certificate gives a bijection points → lines that is a local duality at the freed
  points, which are not collinear. -/

namespace BipartiteDD.LeanAll.TypedHex

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.Typed
open SimpleGraph Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {p : ℕ} [hp : Fact p.Prime]

/-! ## Elements of `H(p)` -/

theorem base_hex : Base (hexInc (F := ZMod p)) := by
  have hG := HexagonEven.genPolygonGraph_hexagon_even (F := ZMod p)
  exact ⟨pl_of_polygon hG, p2_of_polygon hG, l2_of_polygon hG⟩

theorem co_inl {r x : SPt (ZMod p)} :
    Co (hexInc (F := ZMod p)) (.inl r) (.inl x) ↔ Coll hexInc r x := by
  constructor
  · rintro ⟨hne, z, h1, h2⟩
    rcases z with z | l
    · exact absurd h1 Hexagon.incGraph_not_adj_inl_inl
    · exact ⟨fun h => hne (by rw [h]), l, Hexagon.incGraph_adj_inl_inr.1 h1, Hexagon.incGraph_adj_inr_inl.1 h2⟩
  · rintro ⟨hne, l, h1, h2⟩
    exact ⟨by simpa using hne, .inr l, Hexagon.incGraph_adj_inl_inr.2 h1, Hexagon.incGraph_adj_inr_inl.2 h2⟩

theorem co_inr {l m : HLine (ZMod p)} :
    Co (hexInc (F := ZMod p)) (.inr l) (.inr m) ↔ Conc hexInc l m := by
  constructor
  · rintro ⟨hne, z, h1, h2⟩
    rcases z with x | z
    · exact ⟨fun h => hne (by rw [h]), x, Hexagon.incGraph_adj_inr_inl.1 h1, Hexagon.incGraph_adj_inl_inr.1 h2⟩
    · exact absurd h1 Hexagon.incGraph_not_adj_inr_inr
  · rintro ⟨hne, x, h1, h2⟩
    exact ⟨by simpa using hne, .inl x, Hexagon.incGraph_adj_inr_inl.2 h1, Hexagon.incGraph_adj_inl_inr.2 h2⟩

theorem not_co_inl_inr {r : SPt (ZMod p)} {l : HLine (ZMod p)} : ¬ Co (hexInc (F := ZMod p)) (.inl r) (.inr l) :=
  fun h => by have := h.colE_eq; simp [colE] at this

theorem not_co_inr_inl {r : SPt (ZMod p)} {l : HLine (ZMod p)} : ¬ Co (hexInc (F := ZMod p)) (.inr l) (.inl r) :=
  fun h => by have := h.colE_eq; simp [colE] at this

/-- Points to lines by `τ`, lines to points by `τ⁻¹`. -/
def swapE {P L : Type*} (τ : P ≃ L) : P ⊕ L ≃ P ⊕ L :=
  (Equiv.sumCongr τ τ.symm).trans (Equiv.sumComm L P)

@[simp] theorem swapE_inl {P L : Type*} (τ : P ≃ L) (x : P) : swapE τ (.inl x) = .inr (τ x) := rfl
@[simp] theorem swapE_inr {P L : Type*} (τ : P ≃ L) (l : L) : swapE τ (.inr l) = .inl (τ.symm l) := rfl
@[simp] theorem swapE_symm_inl {P L : Type*} (τ : P ≃ L) (x : P) : (swapE τ).symm (.inl x) = .inr (τ x) := rfl
@[simp] theorem swapE_symm_inr {P L : Type*} (τ : P ≃ L) (l : L) : (swapE τ).symm (.inr l) = .inl (τ.symm l) := rfl

/-! ## Friendly freed points -/

/-- Freed point `r` (code `rhc r`) with its lines (entries `(e, α, β)`: `r = α a_e + β b_e`), checked against the
global table `gA, gB, gown` of size `nG`. -/
def rhOK (p nH nG : ℕ) (rhc gown : ℕ → ℕ) (gA gB : ℕ → ℕ) (ents : ℕ → List (ℕ × ℕ × ℕ)) (r : ℕ) : Bool :=
  ptOKb p (rhc r) && (Nat.beq (r + 1) nH || Nat.blt (rhc r) (rhc (r + 1))) && Nat.beq (lenP (ents r)) (p + 1) &&
    sortedLt ((ents r).map (·.1)) &&
    allP (fun t => Nat.blt t.1 nG && Nat.beq (gown t.1) r && linN p (rhc r) (gA t.1) (gB t.1) t.2.1 t.2.2) (ents r)

/-- Entry `e` of the global line table. -/
def glOK (p nG : ℕ) (gA gB : ℕ → ℕ) (e : ℕ) : Bool :=
  lnOKb p (gA e) (gB e) && (Nat.beq (e + 1) nG || Nat.blt (plCode p (gA e) (gB e)) (plCode p (gA (e + 1)) (gB (e + 1))))

section Friendly

variable {nH nG : ℕ} {rhc gown gA gB : ℕ → ℕ} {ents : ℕ → List (ℕ × ℕ × ℕ)}

theorem lnOK_of_gl (h : ∀ e < nG, glOK p nG gA gB e = true) : ∀ e < nG, LnOK p (gA e) (gB e) := by
  intro e he; have := h e he; simp only [glOK, Bool.and_eq_true] at this; exact lnOKb_spec this.1

theorem gl_inj (h : ∀ e < nG, glOK p nG gA gB e = true) :
    ∀ e < nG, ∀ e' < nG, lineOf p (gA e) (gB e) = lineOf p (gA e') (gB e') → e = e' := by
  intro e he e' he' hl
  have hinc : ∀ e, e + 1 < nG → plCode p (gA e) (gB e) < plCode p (gA (e + 1)) (gB (e + 1)) := by
    intro e he
    have := h e (by omega); simp only [glOK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.2 he)
  exact inj_of_succ (f := fun e => plCode p (gA e) (gB e)) hinc e he e' he'
    (lineOf_inj (lnOK_of_gl h e he) (lnOK_of_gl h e' he') hl)

theorem rh_pt (h : ∀ r < nH, rhOK p nH nG rhc gown gA gB ents r = true) : ∀ r < nH, PtOK p (rhc r) := by
  intro r hr; have := h r hr; simp only [rhOK, Bool.and_eq_true] at this; exact ptOKb_spec this.1.1.1.1

theorem rh_inj (h : ∀ r < nH, rhOK p nH nG rhc gown gA gB ents r = true) :
    ∀ r < nH, ∀ r' < nH, ptOf p (rhc r) = ptOf p (rhc r') → r = r' := by
  intro r hr r' hr' he
  have hinc : ∀ r, r + 1 < nH → rhc r < rhc (r + 1) := by
    intro r hr; have := h r (by omega); simp only [rhOK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.1.1.1.2 hr)
  exact inj_of_succ hinc r hr r' hr' (ptOf_inj (rh_pt h r hr) (rh_pt h r' hr') he)

/-- No two friendly freed points are collinear. -/
theorem rh_noncoll (h : ∀ r < nH, rhOK p nH nG rhc gown gA gB ents r = true)
    (hg : ∀ e < nG, glOK p nG gA gB e = true) :
    ∀ r < nH, ∀ r' < nH, ¬ Coll hexInc (ptOf p (rhc r)) (ptOf p (rhc r')) := by
  have key : ∀ r < nH, ∀ W, hexInc (ptOf p (rhc r)) W →
      ∃ t ∈ ents r, t.1 < nG ∧ gown t.1 = r ∧ W = lineOf p (gA t.1) (gB t.1) := by
    intro r hr W hW
    have hr' := h r hr
    simp only [rhOK, Bool.and_eq_true, Nat.beq_eq, lenP_eq, allP_eq, List.all_eq_true, Nat.blt_eq] at hr'
    obtain ⟨⟨⟨⟨-, -⟩, hlen⟩, hsrt⟩, hent⟩ := hr'
    have hent' : ∀ t ∈ ents r, t.1 < nG ∧ gown t.1 = r ∧ linN p (rhc r) (gA t.1) (gB t.1) t.2.1 t.2.2 = true :=
      fun t ht => by obtain ⟨⟨h1, h2⟩, h3⟩ := hent t ht; exact ⟨h1, h2, h3⟩
    have hmem : W ∈ (ents r).map (fun t => lineOf p (gA t.1) (gB t.1)) := by
      refine mem_of_card (card_lns _) _ (by rw [List.length_map, hlen]) ?_ ?_ W hW
      · exact nodup_map_of (nodup_of_sortedLt hsrt) (fun t ht t' ht' htt =>
          gl_inj hg _ (hent' t ht).1 _ (hent' t' ht').1 htt)
      · intro W' hW'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hW'
        exact inc_of_lin (rh_pt h r hr) (lnOK_of_gl hg _ (hent' t ht).1) (hent' t ht).2.2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
    exact ⟨t, ht, (hent' t ht).1, (hent' t ht).2.1, rfl⟩
  rintro r hr r' hr' ⟨hne, W, h1, h2⟩
  obtain ⟨t, -, ht1, ht2, rfl⟩ := key r hr W h1
  obtain ⟨t', -, ht1', ht2', he⟩ := key r' hr' _ h2
  have := gl_inj hg _ ht1 _ ht1' he
  rw [this, ht2'] at ht2
  exact hne (by rw [ht2])

end Friendly

/-! ## Friendly freed lines -/

/-- Freed line `l` (basis `rla l, rlb l`) with its points (entries `(e, α, β)`: point `e` of the global table is
`α a + β b`). -/
def rlOK (p nL nP : ℕ) (rla rlb gp gpown : ℕ → ℕ) (ents : ℕ → List (ℕ × ℕ × ℕ)) (l : ℕ) : Bool :=
  lnOKb p (rla l) (rlb l) &&
    (Nat.beq (l + 1) nL || Nat.blt (plCode p (rla l) (rlb l)) (plCode p (rla (l + 1)) (rlb (l + 1)))) &&
    Nat.beq (lenP (ents l)) (p + 1) && sortedLt ((ents l).map (·.1)) &&
    allP (fun t => Nat.blt t.1 nP && Nat.beq (gpown t.1) l && linN p (gp t.1) (rla l) (rlb l) t.2.1 t.2.2) (ents l)

/-- Entry `e` of the global point table. -/
def gpOK (p nP : ℕ) (gp : ℕ → ℕ) (e : ℕ) : Bool :=
  ptOKb p (gp e) && (Nat.beq (e + 1) nP || Nat.blt (gp e) (gp (e + 1)))

section FriendlyL

variable {nL nP : ℕ} {rla rlb gp gpown : ℕ → ℕ} {ents : ℕ → List (ℕ × ℕ × ℕ)}

theorem ptOK_of_gp (h : ∀ e < nP, gpOK p nP gp e = true) : ∀ e < nP, PtOK p (gp e) := by
  intro e he; have := h e he; simp only [gpOK, Bool.and_eq_true] at this; exact ptOKb_spec this.1

theorem gp_inj (h : ∀ e < nP, gpOK p nP gp e = true) :
    ∀ e < nP, ∀ e' < nP, ptOf p (gp e) = ptOf p (gp e') → e = e' := by
  intro e he e' he' hl
  have hinc : ∀ e, e + 1 < nP → gp e < gp (e + 1) := by
    intro e he
    have := h e (by omega); simp only [gpOK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.2 he)
  exact inj_of_succ hinc e he e' he' (ptOf_inj (ptOK_of_gp h e he) (ptOK_of_gp h e' he') hl)

theorem rl_ln (h : ∀ l < nL, rlOK p nL nP rla rlb gp gpown ents l = true) : ∀ l < nL, LnOK p (rla l) (rlb l) := by
  intro l hl; have := h l hl; simp only [rlOK, Bool.and_eq_true] at this; exact lnOKb_spec this.1.1.1.1

theorem rl_inj (h : ∀ l < nL, rlOK p nL nP rla rlb gp gpown ents l = true) :
    ∀ l < nL, ∀ l' < nL, lineOf p (rla l) (rlb l) = lineOf p (rla l') (rlb l') → l = l' := by
  intro l hl l' hl' he
  have hinc : ∀ l, l + 1 < nL → plCode p (rla l) (rlb l) < plCode p (rla (l + 1)) (rlb (l + 1)) := by
    intro l hl; have := h l (by omega); simp only [rlOK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.1.1.1.2 hl)
  exact inj_of_succ (f := fun l => plCode p (rla l) (rlb l)) hinc l hl l' hl'
    (lineOf_inj (rl_ln h l hl) (rl_ln h l' hl') he)

/-- No two friendly freed lines are concurrent. -/
theorem rl_noncon (h : ∀ l < nL, rlOK p nL nP rla rlb gp gpown ents l = true)
    (hg : ∀ e < nP, gpOK p nP gp e = true) :
    ∀ l < nL, ∀ l' < nL, ¬ Conc hexInc (lineOf p (rla l) (rlb l)) (lineOf p (rla l') (rlb l')) := by
  have key : ∀ l < nL, ∀ x, hexInc x (lineOf p (rla l) (rlb l)) →
      ∃ t ∈ ents l, t.1 < nP ∧ gpown t.1 = l ∧ x = ptOf p (gp t.1) := by
    intro l hl x hx
    have hl' := h l hl
    simp only [rlOK, Bool.and_eq_true, Nat.beq_eq, lenP_eq, allP_eq, List.all_eq_true, Nat.blt_eq] at hl'
    obtain ⟨⟨⟨⟨-, -⟩, hlen⟩, hsrt⟩, hent⟩ := hl'
    have hent' : ∀ t ∈ ents l, t.1 < nP ∧ gpown t.1 = l ∧ linN p (gp t.1) (rla l) (rlb l) t.2.1 t.2.2 = true :=
      fun t ht => by obtain ⟨⟨h1, h2⟩, h3⟩ := hent t ht; exact ⟨h1, h2, h3⟩
    have hmem : x ∈ (ents l).map (fun t => ptOf p (gp t.1)) := by
      refine mem_of_card (card_pts _) _ (by rw [List.length_map, hlen]) ?_ ?_ x hx
      · exact nodup_map_of (nodup_of_sortedLt hsrt) (fun t ht t' ht' htt =>
          gp_inj hg _ (hent' t ht).1 _ (hent' t' ht').1 htt)
      · intro x' hx'
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx'
        exact inc_of_lin (ptOK_of_gp hg _ (hent' t ht).1) (rl_ln h l hl) (hent' t ht).2.2
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
    exact ⟨t, ht, (hent' t ht).1, (hent' t ht).2.1, rfl⟩
  rintro l hl l' hl' ⟨hne, x, h1, h2⟩
  obtain ⟨t, -, ht1, ht2, rfl⟩ := key l hl x h1
  obtain ⟨t', -, ht1', ht2', he⟩ := key l' hl' _ h2
  have := gp_inj hg _ ht1 _ ht1' he
  rw [this, ht2'] at ht2
  exact hne (by rw [ht2])

end FriendlyL

/-! ## Local duality from a `HexLocal` certificate -/

theorem local_duality {M m : ℕ} {ptc lnA lnB sg sgi rl : ℕ → ℕ} {rflag : ℕ → Bool} {cert : ℕ → Cert}
    (hG : Glob p M ptc lnA lnB sg sgi) (hR : ∀ v < m, rl v < M ∧ rflag (rl v) = true)
    (hRs : ∀ v, v + 1 < m → rl v < rl (v + 1)) (hC : ∀ v < m, CertSpec p M ptc lnA lnB sg rflag (rl v) (cert v)) :
    ∃ τ : SPt (ZMod p) ≃ HLine (ZMod p),
      (∀ v < m, ∀ y, Coll hexInc (Fp p ptc (rl v)) y ↔ Conc hexInc (τ (Fp p ptc (rl v))) (τ y)) ∧
      (∀ v < m, ∀ v' < m, ¬ Coll hexInc (Fp p ptc (rl v)) (Fp p ptc (rl v'))) ∧
      (∀ v < m, ∀ v' < m, Fp p ptc (rl v) = Fp p ptc (rl v') → v = v') := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  have hcL : Fintype.card (HLine (ZMod p)) = Fintype.card (SPt (ZMod p)) := by
    have := card_lines_eq (inc := hexInc (F := ZMod p)) (k := p + 1) (by omega) (fun x => card_lns x)
      (fun W => card_pts W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have hgi : ∀ i < M, ∀ j < M, Gl p lnA lnB (sg i) = Gl p lnA lnB (sg j) → i = j := by
    intro i hi j hj h
    have := hG.gl_inj _ (hG.sg i hi).1 _ (hG.sg j hj).1 h
    rw [← (hG.sg i hi).2, ← (hG.sg j hj).2, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_extend hcL.symm (Fp p ptc) (fun i => Gl p lnA lnB (sg i)) hG.fp_inj hgi
  refine ⟨σ, fun v hv y => ?_, fun v hv v' hv' hcoll => ?_, fun v hv v' hv' h =>
    inj_of_succ hRs v hv v' hv' (hG.fp_inj _ (hR v hv).1 _ (hR v' hv').1 h)⟩
  · have hir := (hR v hv).1
    have hc := hC v hv
    rw [coll_iff hG hir hc, hσ _ hir, conc_iff hG hir hc]
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
  · have hir := (hR v hv).1
    obtain ⟨x, hx, hxe⟩ := (coll_iff hG hir (hC v hv) _).1 hcoll
    obtain ⟨e, he, hxe'⟩ := List.mem_flatMap.1 hx
    obtain ⟨hxM, -, hfl, -⟩ := ((hC v hv).e2 e he).2.2.2 x hxe'
    have h1 := hG.fp_inj _ (hR v' hv').1 _ hxM hxe
    have h2 := (hR v' hv').2
    rw [h1, hfl] at h2
    exact Bool.false_ne_true h2

end BipartiteDD.LeanAll.TypedHex
