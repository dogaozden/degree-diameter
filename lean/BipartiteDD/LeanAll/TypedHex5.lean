import BipartiteDD.LeanAll.TypedHex
import BipartiteDD.LeanAll.VHub

/-! # Five typed levels `H H^D H H^D H` over `H(p)` (research/squads/cells/d16D7.md, research/cell147/typedmirror)

Levels `0 … 4` of types `H, D, H, D, H`, two matchings (`j = 2`). The six friendly transitions `0→1, 2→3, 4→1`
(points) and `1→2, 3→4, 3→0` (lines) use the identity and free a non-collinear point set `R_H`, resp. a non-concurrent
line set `R_L`. The non-friendly transitions `4→0, 0→2, 2→4` (`H → H`) and `1→3` (`H^D → H^D`) use `swapE τ` for a
bijection `τ` of a `HexLocal` certificate `c` (a local duality at its freed points) and free the points of `c`
(resp. their lines `τ r`, for `1→3`). Every level's free slots are listed in order, and `K` hubs of each kind take
the first `K` of them; the hub graph is a voltage graph (`VHub`). `main5`: a bipartite graph of maximum degree
`p + 3` and diameter at most `7` on `10 (p + 1)(1 + p² + p⁴) + 2K` vertices. -/

namespace BipartiteDD.LeanAll.TypedHex5

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.TypedHex BipartiteDD.LeanAll.VHub
open SimpleGraph Finset
open scoped Classical

set_option linter.unusedSectionVars false

/-- A `HexLocal` certificate. -/
structure LC where
  M : ℕ
  m : ℕ
  ptc : ℕ → ℕ
  lnA : ℕ → ℕ
  lnB : ℕ → ℕ
  sg : ℕ → ℕ
  sgi : ℕ → ℕ
  rl : ℕ → ℕ
  rflag : ℕ → Bool
  cert : ℕ → Cert

variable {p : ℕ} [hp : Fact p.Prime]

/-- What the checks of a certificate give. -/
structure LC.Ok (p : ℕ) [Fact p.Prime] (c : LC) : Prop where
  glob : Glob p c.M c.ptc c.lnA c.lnB c.sg c.sgi
  r : ∀ v < c.m, c.rl v < c.M ∧ c.rflag (c.rl v) = true
  rs : ∀ v, v + 1 < c.m → c.rl v < c.rl (v + 1)
  cs : ∀ v < c.m, CertSpec p c.M c.ptc c.lnA c.lnB c.sg c.rflag (c.rl v) (c.cert v)

/-- The freed points of a certificate. -/
noncomputable def LC.pt (p : ℕ) [Fact p.Prime] (c : LC) (v : ℕ) : SPt (ZMod p) := Fp p c.ptc (c.rl v)

/-! ## Lists -/

/-- The number of occurrences of `x` in `l`. -/
noncomputable def cnt {α : Type*} (x : α) : List α → ℕ
  | [] => 0
  | y :: l => (if y = x then 1 else 0) + cnt x l

theorem cnt_append {α : Type*} (x : α) (l1 l2 : List α) : cnt x (l1 ++ l2) = cnt x l1 + cnt x l2 := by
  induction l1 with
  | nil => simp [cnt]
  | cons y l ih => simp only [List.cons_append, cnt, ih]; ring

theorem cnt_zero {α : Type*} {x : α} {l : List α} (h : x ∉ l) : cnt x l = 0 := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [cnt, if_neg (Ne.symm h.1), ih h.2]

theorem cnt_le_one {α : Type*} (x : α) {l : List α} (h : l.Nodup) : cnt x l ≤ 1 := by
  induction l with
  | nil => simp [cnt]
  | cons y l ih =>
    rw [List.nodup_cons] at h
    simp only [cnt]
    by_cases hy : y = x
    · subst hy; rw [if_pos rfl, cnt_zero h.1]
    · rw [if_neg hy]; simpa using ih h.2

theorem count_eq_cnt {α : Type*} [DecidableEq α] (x : α) (l : List α) : l.count x = cnt x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [List.count_cons, ih, cnt]
    by_cases hy : y = x <;> simp [hy] <;> ring

theorem card_getD_le {α : Type*} (l : List α) (d : α) {K : ℕ} (hK : K ≤ l.length) (x : α) :
    (univ.filter (fun v : Fin K => l.getD v.val d = x)).card ≤ cnt x l := by
  letI := Classical.decEq α
  have h : (univ.filter (fun i : Fin l.length => List.Vector.get (⟨l, rfl⟩ : List.Vector α l.length) i = x)).card =
      l.count x := Fin.card_filter_univ_eq_vector_get_eq_count x (⟨l, rfl⟩ : List.Vector α l.length)
  rw [← count_eq_cnt, ← h]
  refine Finset.card_le_card_of_injOn (fun v => (⟨v.val, by omega⟩ : Fin l.length)) (fun v hv => ?_)
    (fun v _ w _ h => Fin.ext (by simpa using congrArg Fin.val h))
  have hv' := (Finset.mem_filter.1 hv).2
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
  rw [List.getD_eq_getElem _ _ (by omega)] at hv'
  simpa [List.Vector.get] using hv'

theorem mem_of_getD {α : Type*} (l : List α) (d : α) {K : ℕ} (hK : K ≤ l.length) (v : Fin K) :
    l.getD v.val d ∈ l := by
  rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _

theorem count_le_two {α : Type*} {l1 l2 : List α} (h1 : l1.Nodup) (h2 : l2.Nodup) (x : α)
    {A B : Prop} (hA : x ∈ l1 → A) (hB : x ∈ l2 → B) :
    cnt x (l1 ++ l2) ≤ ((Finset.Icc 1 2).filter (fun k : ℕ => (k = 1 ∧ A) ∨ (k = 2 ∧ B))).card := by
  rw [cnt_append]
  have c1 := cnt_le_one x h1
  have c2 := cnt_le_one x h2
  have z1 : ¬ A → cnt x l1 = 0 := fun h => cnt_zero (fun hx => h (hA hx))
  have z2 : ¬ B → cnt x l2 = 0 := fun h => cnt_zero (fun hx => h (hB hx))
  by_cases hA' : A <;> by_cases hB' : B
  · have : (Finset.Icc 1 2).filter (fun k : ℕ => (k = 1 ∧ A) ∨ (k = 2 ∧ B)) = {1, 2} := by
      ext k; simp [hA', hB']; omega
    rw [this]; simp; omega
  · have : (Finset.Icc 1 2).filter (fun k : ℕ => (k = 1 ∧ A) ∨ (k = 2 ∧ B)) = {1} := by
      ext k; simp [hA', hB']; omega
    rw [this, z2 hB']; simp; omega
  · have : (Finset.Icc 1 2).filter (fun k : ℕ => (k = 1 ∧ A) ∨ (k = 2 ∧ B)) = {2} := by
      ext k; simp [hA', hB']; omega
    rw [this, z1 hA']; simp; omega
  · rw [z1 hA', z2 hB']; omega

/-! ## The theorem -/

/-- Level types: lines first on the odd levels. -/
def ty5 (i : ZMod (2 * 2 + 1)) : Bool := decide (i.val % 2 = 1)

theorem lvl5 (i : ZMod (2 * 2 + 1)) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
  fin_cases i
  exacts [Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr (Or.inl rfl)), Or.inr (Or.inr (Or.inr (Or.inl rfl))),
    Or.inr (Or.inr (Or.inr (Or.inr rfl)))]

theorem v0 : (((0 : ZMod (2 * 2 + 1))).val) = 0 := rfl
theorem v1 : (((1 : ZMod (2 * 2 + 1))).val) = 1 := rfl
theorem v2 : (((2 : ZMod (2 * 2 + 1))).val) = 2 := rfl
theorem v3 : (((3 : ZMod (2 * 2 + 1))).val) = 3 := rfl
theorem v4 : (((4 : ZMod (2 * 2 + 1))).val) = 4 := rfl
theorem a0_1 : (((0 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 1 := rfl
theorem a0_2 : (((0 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 2 := rfl
theorem a1_1 : (((1 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 2 := rfl
theorem a1_2 : (((1 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 3 := rfl
theorem a2_1 : (((2 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 3 := rfl
theorem a2_2 : (((2 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 4 := rfl
theorem a3_1 : (((3 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 4 := rfl
theorem a3_2 : (((3 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 0 := rfl
theorem a4_1 : (((4 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 0 := rfl
theorem a4_2 : (((4 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 1 := rfl
theorem s0_1 : (((0 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 4 := rfl
theorem s0_2 : (((0 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 3 := rfl
theorem s1_1 : (((1 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 0 := rfl
theorem s1_2 : (((1 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 4 := rfl
theorem s2_1 : (((2 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 1 := rfl
theorem s2_2 : (((2 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 0 := rfl
theorem s3_1 : (((3 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 2 := rfl
theorem s3_2 : (((3 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 1 := rfl
theorem s4_1 : (((4 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))).val) = 3 := rfl
theorem s4_2 : (((4 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))).val) = 2 := rfl
theorem t0 : ty5 (0 : ZMod (2 * 2 + 1)) = false := rfl
theorem t1 : ty5 (1 : ZMod (2 * 2 + 1)) = true := rfl
theorem t2 : ty5 (2 : ZMod (2 * 2 + 1)) = false := rfl
theorem t3 : ty5 (3 : ZMod (2 * 2 + 1)) = true := rfl
theorem t4 : ty5 (4 : ZMod (2 * 2 + 1)) = false := rfl
theorem ta0_1 : ty5 ((0 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))) = true := rfl
theorem ta0_2 : ty5 ((0 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta1_1 : ty5 ((1 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta1_2 : ty5 ((1 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))) = true := rfl
theorem ta2_1 : ty5 ((2 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))) = true := rfl
theorem ta2_2 : ty5 ((2 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta3_1 : ty5 ((3 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta3_2 : ty5 ((3 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta4_1 : ty5 ((4 : ZMod (2 * 2 + 1)) + ((1 : ℕ) : ZMod (2 * 2 + 1))) = false := rfl
theorem ta4_2 : ty5 ((4 : ZMod (2 * 2 + 1)) + ((2 : ℕ) : ZMod (2 * 2 + 1))) = true := rfl

theorem z0_1 : ((0 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))) = (4 : ZMod (2 * 2 + 1)) := rfl
theorem z0_2 : ((0 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))) = (3 : ZMod (2 * 2 + 1)) := rfl
theorem z1_1 : ((1 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))) = (0 : ZMod (2 * 2 + 1)) := rfl
theorem z1_2 : ((1 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))) = (4 : ZMod (2 * 2 + 1)) := rfl
theorem z2_1 : ((2 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))) = (1 : ZMod (2 * 2 + 1)) := rfl
theorem z2_2 : ((2 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))) = (0 : ZMod (2 * 2 + 1)) := rfl
theorem z3_1 : ((3 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))) = (2 : ZMod (2 * 2 + 1)) := rfl
theorem z3_2 : ((3 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))) = (1 : ZMod (2 * 2 + 1)) := rfl
theorem z4_1 : ((4 : ZMod (2 * 2 + 1)) - ((1 : ℕ) : ZMod (2 * 2 + 1))) = (3 : ZMod (2 * 2 + 1)) := rfl
theorem z4_2 : ((4 : ZMod (2 * 2 + 1)) - ((2 : ℕ) : ZMod (2 * 2 + 1))) = (2 : ZMod (2 * 2 + 1)) := rfl

theorem k12 {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ 2) : k = 1 ∨ k = 2 := by omega

@[simp] theorem colE_swap {P L : Type*} (τ : P ≃ L) (x : P ⊕ L) : colE (swapE τ x) = !colE x := by
  rcases x with x | x <;> rfl

@[simp] theorem colE_swap_symm {P L : Type*} (τ : P ≃ L) (x : P ⊕ L) : colE ((swapE τ).symm x) = !colE x := by
  rcases x with x | x <;> rfl

/-- `σ` of the five levels. -/
noncomputable def sig5 {E : Type*} (s40 s02 s24 s13 : E ≃ E) (i : ZMod (2 * 2 + 1)) (k : ℕ) : E ≃ E :=
  if i.val = 4 ∧ k = 1 then s40 else if i.val = 0 ∧ k = 2 then s02 else if i.val = 2 ∧ k = 2 then s24
  else if i.val = 1 ∧ k = 2 then s13 else Equiv.refl E

/-- The freed sets of the five levels. -/
def R5 {E : Type*} (lH lL l40 l02 l24 l13 : List E) (i : ZMod (2 * 2 + 1)) (k : ℕ) : Set E :=
  if (i.val = 0 ∧ k = 1) ∨ (i.val = 2 ∧ k = 1) ∨ (i.val = 4 ∧ k = 2) then {x | x ∈ lH}
  else if (i.val = 1 ∧ k = 1) ∨ (i.val = 3 ∧ k = 1) ∨ (i.val = 3 ∧ k = 2) then {x | x ∈ lL}
  else if i.val = 4 ∧ k = 1 then {x | x ∈ l40} else if i.val = 0 ∧ k = 2 then {x | x ∈ l02}
  else if i.val = 2 ∧ k = 2 then {x | x ∈ l24} else if i.val = 1 ∧ k = 2 then {x | x ∈ l13} else ∅

/-- The free `A`-slots of each level. -/
def A5 {E : Type*} (lH lL l40 l02 l24 l13 : List E) (i : ZMod (2 * 2 + 1)) : List E :=
  if i.val = 0 then lH ++ l02 else if i.val = 1 then lL ++ l13 else if i.val = 2 then lH ++ l24
  else if i.val = 3 then lL ++ lL else l40 ++ lH

/-- The free `B`-slots of each level. -/
def B5 {E : Type*} (lH lL m40 m02 m24 m13 : List E) (i : ZMod (2 * 2 + 1)) : List E :=
  if i.val = 0 then m40 ++ lL else if i.val = 1 then lH ++ lH else if i.val = 2 then lL ++ m02
  else if i.val = 3 then lH ++ m13 else lL ++ m24

theorem mem_rmap {α : Type*} {n : ℕ} {f : ℕ → α} {x : α} : x ∈ (List.range n).map f ↔ ∃ t < n, f t = x := by
  simp [List.mem_map, List.mem_range]

theorem nodup_rmap {α : Type*} {n : ℕ} {f : ℕ → α} (h : ∀ t < n, ∀ t' < n, f t = f t' → t = t') :
    ((List.range n).map f).Nodup :=
  List.Nodup.map_on (fun t ht t' ht' e => h t (List.mem_range.1 ht) t' (List.mem_range.1 ht') e) List.nodup_range

theorem deg_E (x : SPt (ZMod p) ⊕ HLine (ZMod p)) [Fintype (SPt (ZMod p))] [Fintype (HLine (ZMod p))] :
    (univ.filter ((Hexagon.incGraph (hexInc (F := ZMod p))).Adj x)).card ≤ p + 1 := by
  rcases x with a | l
  · have hP : (univ.filter (hexInc a)).card = p + 1 := by
      rw [← card_lns a, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine le_trans (Finset.card_le_card_of_injOn (fun y => match y with | .inr l => l | .inl _ => Classical.arbitrary _)
      (fun y hy => ?_) (fun y hy y' hy' h => ?_)) hP.le
    · rcases y with y | l
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inl_inl
      · simpa using Hexagon.incGraph_adj_inl_inr.1 (Finset.mem_filter.1 hy).2
    · rcases y with y | l <;> rcases y' with y' | l'
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inl_inl
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inl_inl
      · exact absurd (Finset.mem_filter.1 hy').2 Hexagon.incGraph_not_adj_inl_inl
      · simp only at h; rw [h]
  · have hL : (univ.filter (fun y => hexInc y l)).card = p + 1 := by
      rw [← card_pts l, Nat.card_eq_fintype_card, Fintype.card_subtype]
    refine le_trans (Finset.card_le_card_of_injOn (fun y => match y with | .inl a => a | .inr _ => Classical.arbitrary _)
      (fun y hy => ?_) (fun y hy y' hy' h => ?_)) hL.le
    · rcases y with a | y
      · simpa using Hexagon.incGraph_adj_inr_inl.1 (Finset.mem_filter.1 hy).2
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inr_inr
    · rcases y with a | y <;> rcases y' with a' | y'
      · simp only at h; rw [h]
      · exact absurd (Finset.mem_filter.1 hy').2 Hexagon.incGraph_not_adj_inr_inr
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inr_inr
      · exact absurd (Finset.mem_filter.1 hy).2 Hexagon.incGraph_not_adj_inr_inr


/-- **Five typed levels over `H(p)`.** -/
theorem main5 (p : ℕ) [Fact p.Prime]
    (nH nG : ℕ) (rhc gown gA gB : ℕ → ℕ) (entsH : ℕ → List (ℕ × ℕ × ℕ))
    (hRH : ∀ r < nH, rhOK p nH nG rhc gown gA gB entsH r = true) (hGL : ∀ e < nG, glOK p nG gA gB e = true)
    (nL nP : ℕ) (rla rlb gp gpown : ℕ → ℕ) (entsL : ℕ → List (ℕ × ℕ × ℕ))
    (hRL : ∀ l < nL, rlOK p nL nP rla rlb gp gpown entsL l = true) (hGP : ∀ e < nP, gpOK p nP gp e = true)
    (c40 c02 c24 c13 : LC) (h40 : c40.Ok p) (h02 : c02.Ok p) (h24 : c24.Ok p) (h13 : c13.Ok p)
    (vm vb : ℕ) (E : List (ℕ × ℕ × ℕ)) (hvb : 0 < vb)
    (hHL : LocalSpec (p - 2) (2 * (vb * vm)) (vnb vm vb E) (vcol vb))
    (hHD : (graphF (2 * (vb * vm)) (vnb vm vb E)).ediam ≤ 7)
    (hKA : vb * vm ≤ nH + c02.m ∧ vb * vm ≤ nL + c13.m ∧ vb * vm ≤ nH + c24.m ∧ vb * vm ≤ nL + nL ∧
      vb * vm ≤ c40.m + nH)
    (hKB : vb * vm ≤ c40.m + nL ∧ vb * vm ≤ nH + nH ∧ vb * vm ≤ nL + c02.m ∧ vb * vm ≤ nH + c13.m ∧
      vb * vm ≤ nL + c24.m) :
    ∃ G : SimpleGraph (Fin (10 * ((p + 1) * (1 + p ^ 2 + p ^ 4)) + 2 * (vb * vm))),
      IsBipartiteDegDiam G (p + 3) 7 := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  obtain ⟨τ40, d40, n40, i40⟩ := local_duality h40.glob h40.r h40.rs h40.cs
  obtain ⟨τ02, d02, n02, i02⟩ := local_duality h02.glob h02.r h02.rs h02.cs
  obtain ⟨τ24, d24, n24, i24⟩ := local_duality h24.glob h24.r h24.rs h24.cs
  obtain ⟨τ13, d13, n13, i13⟩ := local_duality h13.glob h13.r h13.rs h13.cs
  -- the element lists
  set lH : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := (List.range nH).map (fun t => .inl (ptOf p (rhc t))) with hlH
  set lL : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
    (List.range nL).map (fun t => .inr (lineOf p (rla t) (rlb t))) with hlL
  set l40 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := (List.range c40.m).map (fun v => .inl (c40.pt p v)) with hl40
  set l02 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := (List.range c02.m).map (fun v => .inl (c02.pt p v)) with hl02
  set l24 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := (List.range c24.m).map (fun v => .inl (c24.pt p v)) with hl24
  set l13 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
    (List.range c13.m).map (fun v => .inr (τ13 (c13.pt p v))) with hl13
  set m40 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
    (List.range c40.m).map (fun v => .inr (τ40 (c40.pt p v))) with hm40
  set m02 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
    (List.range c02.m).map (fun v => .inr (τ02 (c02.pt p v))) with hm02
  set m24 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
    (List.range c24.m).map (fun v => .inr (τ24 (c24.pt p v))) with hm24
  set m13 : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := (List.range c13.m).map (fun v => .inl (c13.pt p v)) with hm13
  set σ := sig5 (swapE τ40) (swapE τ02) (swapE τ24) (swapE τ13) with hσ
  set R := R5 lH lL l40 l02 l24 l13 with hR
  set K := vb * vm with hK
  let dflt : SPt (ZMod p) ⊕ HLine (ZMod p) := .inl (Classical.arbitrary _)
  set slotV : Fin K → ZMod (2 * 2 + 1) → SPt (ZMod p) ⊕ HLine (ZMod p) :=
    fun v i => (A5 lH lL l40 l02 l24 l13 i).getD v.val dflt with hsV
  set slotU : Fin K → ZMod (2 * 2 + 1) → SPt (ZMod p) ⊕ HLine (ZMod p) :=
    fun u i => (B5 lH lL m40 m02 m24 m13 i).getD u.val dflt with hsU
  obtain ⟨hV6, hU6, hNV, hNU⟩ := vhub hvb hHL hHD
  -- membership in the lists
  have mH : ∀ x, x ∈ lH ↔ ∃ t < nH, (.inl (ptOf p (rhc t)) : SPt (ZMod p) ⊕ HLine (ZMod p)) = x := fun x => mem_rmap
  have mL : ∀ x, x ∈ lL ↔ ∃ t < nL, (.inr (lineOf p (rla t) (rlb t)) : SPt (ZMod p) ⊕ HLine (ZMod p)) = x :=
    fun x => mem_rmap
  have cH : ∀ x ∈ lH, colE x = false := by
    intro x hx; obtain ⟨t, -, rfl⟩ := (mH x).1 hx; rfl
  have cL : ∀ x ∈ lL, colE x = true := by
    intro x hx; obtain ⟨t, -, rfl⟩ := (mL x).1 hx; rfl
  have cP : ∀ (c : LC) (f : ℕ → SPt (ZMod p)), ∀ x ∈ (List.range c.m).map (fun v =>
      (.inl (f v) : SPt (ZMod p) ⊕ HLine (ZMod p))), colE x = false := by
    intro c f x hx; obtain ⟨t, -, rfl⟩ := mem_rmap.1 hx; rfl
  have cQ : ∀ (c : LC) (f : ℕ → HLine (ZMod p)), ∀ x ∈ (List.range c.m).map (fun v =>
      (.inr (f v) : SPt (ZMod p) ⊕ HLine (ZMod p))), colE x = true := by
    intro c f x hx; obtain ⟨t, -, rfl⟩ := mem_rmap.1 hx; rfl

  have icc12 : ∀ P : ℕ → Prop, (Finset.Icc 1 2).filter P =
      (Finset.Icc 1 2).filter (fun k : ℕ => (k = 1 ∧ P 1) ∨ (k = 2 ∧ P 2)) := by
    intro P; ext k; simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp⟩; refine ⟨⟨h1, h2⟩, ?_⟩
      rcases k12 h1 h2 with rfl | rfl
      · exact Or.inl ⟨rfl, hp⟩
      · exact Or.inr ⟨rfl, hp⟩
    · rintro ⟨⟨h1, h2⟩, ⟨rfl, hp⟩ | ⟨rfl, hp⟩⟩ <;> exact ⟨⟨by omega, by omega⟩, hp⟩
  have nlH : lH.Nodup := nodup_rmap (fun t ht t' ht' e => rh_inj hRH t ht t' ht' (Sum.inl_injective e))
  have nlL : lL.Nodup := nodup_rmap (fun t ht t' ht' e => rl_inj hRL t ht t' ht' (Sum.inr_injective e))
  have nP : ∀ (c : LC) (f : ℕ → SPt (ZMod p)), (∀ v < c.m, ∀ v' < c.m, f v = f v' → v = v') →
      ((List.range c.m).map (fun v => (.inl (f v) : SPt (ZMod p) ⊕ HLine (ZMod p)))).Nodup :=
    fun c f hf => nodup_rmap (fun t ht t' ht' e => hf t ht t' ht' (Sum.inl_injective e))
  have nQ : ∀ (c : LC) (f : ℕ → HLine (ZMod p)), (∀ v < c.m, ∀ v' < c.m, f v = f v' → v = v') →
      ((List.range c.m).map (fun v => (.inr (f v) : SPt (ZMod p) ⊕ HLine (ZMod p)))).Nodup :=
    fun c f hf => nodup_rmap (fun t ht t' ht' e => hf t ht t' ht' (Sum.inr_injective e))
  have nl40 : l40.Nodup := nP c40 _ i40
  have nl02 : l02.Nodup := nP c02 _ i02
  have nl24 : l24.Nodup := nP c24 _ i24
  have nm13 : m13.Nodup := nP c13 _ i13
  have nm40 : m40.Nodup := nQ c40 _ (fun v hv v' hv' e => i40 v hv v' hv' (τ40.injective e))
  have nm02 : m02.Nodup := nQ c02 _ (fun v hv v' hv' e => i02 v hv v' hv' (τ02.injective e))
  have nm24 : m24.Nodup := nQ c24 _ (fun v hv v' hv' e => i24 v hv v' hv' (τ24.injective e))
  have nl13 : l13.Nodup := nQ c13 _ (fun v hv v' hv' e => i13 v hv v' hv' (τ13.injective e))
  have len : lH.length = nH ∧ lL.length = nL ∧ l40.length = c40.m ∧ l02.length = c02.m ∧ l24.length = c24.m ∧
      l13.length = c13.m ∧ m40.length = c40.m ∧ m02.length = c02.m ∧ m24.length = c24.m ∧ m13.length = c13.m := by
    simp [hlH, hlL, hl40, hl02, hl24, hl13, hm40, hm02, hm24, hm13]
  have hmaps : ∀ i (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ x, colE x = ty5 i → colE (σ i k x) = !ty5 (i + k) := by
    intro i k hk1 hk2 x hx
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k12 hk1 hk2 with rfl | rfl <;>
      simp only [hσ, sig5, v0, v1, v2, v3, v4, ta0_1, ta0_2, ta1_1, ta1_2, ta2_1, ta2_2, ta3_1, ta3_2, ta4_1, ta4_2, t0, t1, t2, t3, t4, Equiv.refl_apply, colE_swap] at hx ⊢ <;> simp [hx]
  have honto : ∀ i (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ y, colE y = !ty5 (i + k) → colE ((σ i k).symm y) = ty5 i := by
    intro i k hk1 hk2 y hy
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k12 hk1 hk2 with rfl | rfl <;>
      simp only [hσ, sig5, v0, v1, v2, v3, v4, ta0_1, ta0_2, ta1_1, ta1_2, ta2_1, ta2_2, ta3_1, ta3_2, ta4_1, ta4_2, t0, t1, t2, t3, t4, Equiv.refl_symm, Equiv.refl_apply, colE_swap_symm] at hy ⊢ <;>
      simp [hy]
  have hrA : ∀ i (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ x ∈ R i k, colE x = ty5 i := by
    intro i k hk1 hk2 x hx
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k12 hk1 hk2 with rfl | rfl <;>
      simp only [hR, R5, v0, v1, v2, v3, v4, t0, t1, t2, t3, t4, Set.mem_setOf_eq] at hx ⊢ <;> simp at hx ⊢
    all_goals first
      | exact cH x hx | exact cL x hx | exact cP _ _ x hx | exact cQ _ _ x hx

  have eσ01 : σ (0 : ZMod (2 * 2 + 1)) 1 = Equiv.refl _ := by simp [hσ, sig5, v0]
  have eR01 : R (0 : ZMod (2 * 2 + 1)) 1 = {x | x ∈ lH} := by simp [hR, R5, v0]
  have eσ02 : σ (0 : ZMod (2 * 2 + 1)) 2 = swapE τ02 := by simp [hσ, sig5, v0]
  have eR02 : R (0 : ZMod (2 * 2 + 1)) 2 = {x | x ∈ l02} := by simp [hR, R5, v0]
  have eA0 : A5 lH lL l40 l02 l24 l13 (0 : ZMod (2 * 2 + 1)) = lH ++ l02 := by simp [A5, v0]
  have eB0 : B5 lH lL m40 m02 m24 m13 (0 : ZMod (2 * 2 + 1)) = m40 ++ lL := by simp [B5, v0]
  have eσ11 : σ (1 : ZMod (2 * 2 + 1)) 1 = Equiv.refl _ := by simp [hσ, sig5, v1]
  have eR11 : R (1 : ZMod (2 * 2 + 1)) 1 = {x | x ∈ lL} := by simp [hR, R5, v1]
  have eσ12 : σ (1 : ZMod (2 * 2 + 1)) 2 = swapE τ13 := by simp [hσ, sig5, v1]
  have eR12 : R (1 : ZMod (2 * 2 + 1)) 2 = {x | x ∈ l13} := by simp [hR, R5, v1]
  have eA1 : A5 lH lL l40 l02 l24 l13 (1 : ZMod (2 * 2 + 1)) = lL ++ l13 := by simp [A5, v1]
  have eB1 : B5 lH lL m40 m02 m24 m13 (1 : ZMod (2 * 2 + 1)) = lH ++ lH := by simp [B5, v1]
  have eσ21 : σ (2 : ZMod (2 * 2 + 1)) 1 = Equiv.refl _ := by simp [hσ, sig5, v2]
  have eR21 : R (2 : ZMod (2 * 2 + 1)) 1 = {x | x ∈ lH} := by simp [hR, R5, v2]
  have eσ22 : σ (2 : ZMod (2 * 2 + 1)) 2 = swapE τ24 := by simp [hσ, sig5, v2]
  have eR22 : R (2 : ZMod (2 * 2 + 1)) 2 = {x | x ∈ l24} := by simp [hR, R5, v2]
  have eA2 : A5 lH lL l40 l02 l24 l13 (2 : ZMod (2 * 2 + 1)) = lH ++ l24 := by simp [A5, v2]
  have eB2 : B5 lH lL m40 m02 m24 m13 (2 : ZMod (2 * 2 + 1)) = lL ++ m02 := by simp [B5, v2]
  have eσ31 : σ (3 : ZMod (2 * 2 + 1)) 1 = Equiv.refl _ := by simp [hσ, sig5, v3]
  have eR31 : R (3 : ZMod (2 * 2 + 1)) 1 = {x | x ∈ lL} := by simp [hR, R5, v3]
  have eσ32 : σ (3 : ZMod (2 * 2 + 1)) 2 = Equiv.refl _ := by simp [hσ, sig5, v3]
  have eR32 : R (3 : ZMod (2 * 2 + 1)) 2 = {x | x ∈ lL} := by simp [hR, R5, v3]
  have eA3 : A5 lH lL l40 l02 l24 l13 (3 : ZMod (2 * 2 + 1)) = lL ++ lL := by simp [A5, v3]
  have eB3 : B5 lH lL m40 m02 m24 m13 (3 : ZMod (2 * 2 + 1)) = lH ++ m13 := by simp [B5, v3]
  have eσ41 : σ (4 : ZMod (2 * 2 + 1)) 1 = swapE τ40 := by simp [hσ, sig5, v4]
  have eR41 : R (4 : ZMod (2 * 2 + 1)) 1 = {x | x ∈ l40} := by simp [hR, R5, v4]
  have eσ42 : σ (4 : ZMod (2 * 2 + 1)) 2 = Equiv.refl _ := by simp [hσ, sig5, v4]
  have eR42 : R (4 : ZMod (2 * 2 + 1)) 2 = {x | x ∈ lH} := by simp [hR, R5, v4]
  have eA4 : A5 lH lL l40 l02 l24 l13 (4 : ZMod (2 * 2 + 1)) = l40 ++ lH := by simp [A5, v4]
  have eB4 : B5 lH lL m40 m02 m24 m13 (4 : ZMod (2 * 2 + 1)) = lL ++ m24 := by simp [B5, v4]
  have hr1 : ∀ i (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ r ∈ R i k, ∀ s ∈ R i k, ¬ Co hexInc r s := by
    have pH : ∀ r ∈ lH, ∀ s ∈ lH, ¬ Co hexInc r s := by
      intro r hr s hs hco
      obtain ⟨t, ht, rfl⟩ := (mH r).1 hr; obtain ⟨t', ht', rfl⟩ := (mH s).1 hs
      exact rh_noncoll hRH hGL t ht t' ht' (co_inl.1 hco)
    have pL : ∀ r ∈ lL, ∀ s ∈ lL, ¬ Co hexInc r s := by
      intro r hr s hs hco
      obtain ⟨t, ht, rfl⟩ := (mL r).1 hr; obtain ⟨t', ht', rfl⟩ := (mL s).1 hs
      exact rl_noncon hRL hGP t ht t' ht' (co_inr.1 hco)
    have pP : ∀ (c : LC), (∀ v < c.m, ∀ v' < c.m, ¬ Coll hexInc (c.pt p v) (c.pt p v')) →
        ∀ r ∈ (List.range c.m).map (fun v => (.inl (c.pt p v) : SPt (ZMod p) ⊕ HLine (ZMod p))),
        ∀ s ∈ (List.range c.m).map (fun v => (.inl (c.pt p v) : SPt (ZMod p) ⊕ HLine (ZMod p))),
        ¬ Co hexInc r s := by
      intro c hc r hr s hs hco
      obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hr; obtain ⟨t', ht', rfl⟩ := mem_rmap.1 hs
      exact hc t ht t' ht' (co_inl.1 hco)
    have p13 : ∀ r ∈ l13, ∀ s ∈ l13, ¬ Co hexInc r s := by
      intro r hr s hs hco
      obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hr; obtain ⟨t', ht', rfl⟩ := mem_rmap.1 hs
      exact n13 t ht t' ht' ((d13 t ht _).2 (co_inr.1 hco))
    intro i k hk1 hk2 r hr s hs
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k12 hk1 hk2 with rfl | rfl <;>
      simp only [hR, R5, v0, v1, v2, v3, v4, Set.mem_setOf_eq] at hr hs <;> simp at hr hs
    all_goals first
      | exact pH r hr s hs | exact pL r hr s hs | exact p13 r hr s hs
      | exact pP c40 n40 r hr s hs | exact pP c02 n02 r hr s hs | exact pP c24 n24 r hr s hs
  have hr2 : ∀ i (k : ℕ), 1 ≤ k → k ≤ 2 → ∀ r ∈ R i k, ∀ x, Co hexInc r x ↔ Co hexInc (σ i k r) (σ i k x) := by
    have qP : ∀ (c : LC) (τ : SPt (ZMod p) ≃ HLine (ZMod p)),
        (∀ v < c.m, ∀ y, Coll hexInc (c.pt p v) y ↔ Conc hexInc (τ (c.pt p v)) (τ y)) →
        ∀ r ∈ (List.range c.m).map (fun v => (.inl (c.pt p v) : SPt (ZMod p) ⊕ HLine (ZMod p))),
        ∀ x, Co hexInc r x ↔ Co hexInc (swapE τ r) (swapE τ x) := by
      intro c τ hc r hr x
      obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hr
      rcases x with y | l
      · rw [swapE_inl, swapE_inl, co_inl, co_inr]; exact hc t ht y
      · rw [swapE_inl, swapE_inr]
        exact iff_of_false not_co_inl_inr not_co_inr_inl
    have q13 : ∀ r ∈ l13, ∀ x, Co hexInc r x ↔ Co hexInc (swapE τ13 r) (swapE τ13 x) := by
      intro r hr x
      obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hr
      rcases x with y | l
      · rw [swapE_inl, swapE_inr]
        exact iff_of_false not_co_inr_inl not_co_inl_inr
      · rw [swapE_inr, swapE_inr, co_inr, co_inl, Equiv.symm_apply_apply]
        have := d13 t ht (τ13.symm l)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
    intro i k hk1 hk2 r hr x
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> rcases k12 hk1 hk2 with rfl | rfl
    all_goals first
      | (rw [eσ01]; exact Iff.rfl) | (rw [eσ11]; exact Iff.rfl) | (rw [eσ21]; exact Iff.rfl)
      | (rw [eσ31]; exact Iff.rfl) | (rw [eσ32]; exact Iff.rfl) | (rw [eσ42]; exact Iff.rfl)
      | (rw [eσ41]; rw [eR41] at hr; exact qP c40 τ40 d40 r hr x)
      | (rw [eσ02]; rw [eR02] at hr; exact qP c02 τ02 d02 r hr x)
      | (rw [eσ22]; rw [eR22] at hr; exact qP c24 τ24 d24 r hr x)
      | (rw [eσ12]; rw [eR12] at hr; exact q13 r hr x)
  have hlenA : ∀ i, K ≤ (A5 lH lL l40 l02 l24 l13 i).length := by
    intro i
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> simp only [A5, v0, v1, v2, v3, v4] <;> simp [len] <;> omega
  have hlenB : ∀ i, K ≤ (B5 lH lL m40 m02 m24 m13 i).length := by
    intro i
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl <;> simp only [B5, v0, v1, v2, v3, v4] <;> simp [len] <;> omega
  have hslotA : ∀ v i, colE (slotV v i) = ty5 i := by
    intro v i
    have hm := mem_of_getD (A5 lH lL l40 l02 l24 l13 i) dflt (hlenA i) v
    show colE ((A5 lH lL l40 l02 l24 l13 i).getD v.val dflt) = ty5 i
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl
    · rw [eA0] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cH _ hm
      · exact cP _ _ _ hm
    · rw [eA1] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cL _ hm
      · exact cQ _ _ _ hm
    · rw [eA2] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cH _ hm
      · exact cP _ _ _ hm
    · rw [eA3] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cL _ hm
      · exact cL _ hm
    · rw [eA4] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cP _ _ _ hm
      · exact cH _ hm
  have hslotB : ∀ u i, colE (slotU u i) = !ty5 i := by
    intro u i
    have hm := mem_of_getD (B5 lH lL m40 m02 m24 m13 i) dflt (hlenB i) u
    show colE ((B5 lH lL m40 m02 m24 m13 i).getD u.val dflt) = !ty5 i
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl
    · rw [eB0] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cQ _ _ _ hm
      · exact cL _ hm
    · rw [eB1] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cH _ hm
      · exact cH _ hm
    · rw [eB2] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cL _ hm
      · exact cQ _ _ _ hm
    · rw [eB3] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cH _ hm
      · exact cP _ _ _ hm
    · rw [eB4] at hm ⊢; rcases List.mem_append.1 hm with hm | hm
      · exact cL _ hm
      · exact cQ _ _ _ hm

  have hSV : ∀ i x, (univ.filter (fun v => slotV v i = x)).card ≤
      ((Finset.Icc 1 2).filter (fun k => x ∈ R i k)).card := by
    intro i x
    have h1 : (univ.filter (fun v => slotV v i = x)).card ≤ cnt x (A5 lH lL l40 l02 l24 l13 i) := by
      simp only [hsV]; convert card_getD_le (A5 lH lL l40 l02 l24 l13 i) dflt (hlenA i) x
    refine le_trans h1 ?_
    rw [icc12]
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl
    · rw [eA0]; exact count_le_two nlH nl02 x (A := x ∈ R 0 1) (B := x ∈ R 0 2)
        (fun h => by rw [eR01]; exact h) (fun h => by rw [eR02]; exact h)
    · rw [eA1]; exact count_le_two nlL nl13 x (A := x ∈ R 1 1) (B := x ∈ R 1 2)
        (fun h => by rw [eR11]; exact h) (fun h => by rw [eR12]; exact h)
    · rw [eA2]; exact count_le_two nlH nl24 x (A := x ∈ R 2 1) (B := x ∈ R 2 2)
        (fun h => by rw [eR21]; exact h) (fun h => by rw [eR22]; exact h)
    · rw [eA3]; exact count_le_two nlL nlL x (A := x ∈ R 3 1) (B := x ∈ R 3 2)
        (fun h => by rw [eR31]; exact h) (fun h => by rw [eR32]; exact h)
    · rw [eA4]; exact count_le_two nl40 nlH x (A := x ∈ R 4 1) (B := x ∈ R 4 2)
        (fun h => by rw [eR41]; exact h) (fun h => by rw [eR42]; exact h)
  have pM : ∀ (c : LC) (τ : SPt (ZMod p) ≃ HLine (ZMod p)) y,
      y ∈ (List.range c.m).map (fun v => (.inr (τ (c.pt p v)) : SPt (ZMod p) ⊕ HLine (ZMod p))) →
      (swapE τ).symm y ∈ (List.range c.m).map (fun v => (.inl (c.pt p v) : SPt (ZMod p) ⊕ HLine (ZMod p))) := by
    intro c τ y hy
    obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hy
    rw [swapE_symm_inr, Equiv.symm_apply_apply]
    exact mem_rmap.2 ⟨t, ht, rfl⟩
  have pM13 : ∀ y, y ∈ m13 → (swapE τ13).symm y ∈ l13 := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := mem_rmap.1 hy
    rw [swapE_symm_inl]
    exact mem_rmap.2 ⟨t, ht, rfl⟩
  have hSU : ∀ i y, (univ.filter (fun u => slotU u i = y)).card ≤
      ((Finset.Icc 1 2).filter (fun k : ℕ => (σ (i - (k : ZMod (2 * 2 + 1))) k).symm y ∈
        R (i - (k : ZMod (2 * 2 + 1))) k)).card := by
    intro i y
    have h1 : (univ.filter (fun u => slotU u i = y)).card ≤ cnt y (B5 lH lL m40 m02 m24 m13 i) := by
      simp only [hsU]; convert card_getD_le (B5 lH lL m40 m02 m24 m13 i) dflt (hlenB i) y
    refine le_trans h1 ?_
    rw [icc12]
    rcases lvl5 i with rfl | rfl | rfl | rfl | rfl
    · rw [eB0]; simp only [z0_1, z0_2]
      exact count_le_two nm40 nlL y (A := (σ 4 1).symm y ∈ R 4 1) (B := (σ 3 2).symm y ∈ R 3 2)
        (fun h => by rw [eσ41, eR41]; exact pM c40 τ40 y h)
        (fun h => by rw [eσ32, eR32]; exact h)
    · rw [eB1]; simp only [z1_1, z1_2]
      exact count_le_two nlH nlH y (A := (σ 0 1).symm y ∈ R 0 1) (B := (σ 4 2).symm y ∈ R 4 2)
        (fun h => by rw [eσ01, eR01]; exact h) (fun h => by rw [eσ42, eR42]; exact h)
    · rw [eB2]; simp only [z2_1, z2_2]
      exact count_le_two nlL nm02 y (A := (σ 1 1).symm y ∈ R 1 1) (B := (σ 0 2).symm y ∈ R 0 2)
        (fun h => by rw [eσ11, eR11]; exact h)
        (fun h => by rw [eσ02, eR02]; exact pM c02 τ02 y h)
    · rw [eB3]; simp only [z3_1, z3_2]
      exact count_le_two nlH nm13 y (A := (σ 2 1).symm y ∈ R 2 1) (B := (σ 1 2).symm y ∈ R 1 2)
        (fun h => by rw [eσ21, eR21]; exact h)
        (fun h => by rw [eσ12, eR12]; exact pM13 y h)
    · rw [eB4]; simp only [z4_1, z4_2]
      exact count_le_two nlL nm24 y (A := (σ 3 1).symm y ∈ R 3 1) (B := (σ 2 2).symm y ∈ R 2 2)
        (fun h => by rw [eσ31, eR31]; exact h)
        (fun h => by rw [eσ22, eR22]; exact pM c24 τ24 y h)
  have H : THyp hexInc 2 ty5 σ R slotV slotU (vNS vm vb E) :=
    ⟨base_hex, hmaps, honto, hrA, hr1, hr2, hslotA, hslotB, fun v v' => Or.inr (hV6 v v'),
      fun u u' => Or.inr (hU6 u u')⟩
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have main := H.exists_graph (q := p) (fun x => deg_E x) (fun i x => by convert hSV i x)
    (fun i y => by convert hSU i y) (fun v => by convert hNV v)
    (fun u => by convert hNU u) hp2
  have hcP : Fintype.card (SPt (ZMod p)) = (p + 1) * (1 + p ^ 2 + p ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_spt_eq, ZMod.card]
  have hcL : Fintype.card (HLine (ZMod p)) = Fintype.card (SPt (ZMod p)) := by
    have := card_lines_eq (inc := hexInc (F := ZMod p)) (k := p + 1) (by omega) (fun x => card_lns x)
      (fun W => card_pts W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have e : (2 * 2 + 1) * (Fintype.card (SPt (ZMod p)) + Fintype.card (HLine (ZMod p))) + Fintype.card (Fin K) +
      Fintype.card (Fin K) = 10 * ((p + 1) * (1 + p ^ 2 + p ^ 4)) + 2 * (vb * vm) := by
    rw [hcL, hcP, Fintype.card_fin]; ring
  rw [e, show p + 1 + 2 = p + 3 by ring] at main
  exact main


end BipartiteDD.LeanAll.TypedHex5
