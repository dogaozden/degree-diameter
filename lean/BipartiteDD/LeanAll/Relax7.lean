import BipartiteDD.LeanAll.RTyped
import BipartiteDD.LeanAll.TypedHex5
import BipartiteDD.LeanAll.BitBFS

/-! # Seven typed levels over `H(p)` with relaxed friendly sets (research/d15D7b/RELAXED.md)

Levels `0 … 6` of types `TY a` (`false`: `H`, the points are the `A`-class; `true`: `H^D`), three matchings
(`j = 3`). Transition `a → a + k` is number `trn a k = 3a + k - 1`; it frees the elements `den (kF tr) (cF tr t)`
(`t < nT tr`; points by code, lines by basis) and their images `den (kI tr) (cI tr t)`. A transition between levels
of different types (friendly) uses the identity; its freed set may contain pairs of collinear points (concurrent
lines), each element with at most one partner `pr tr t`, and every pair is served by a point-side and a line-side hub
whose other slots are incident with the partner. The other transitions use `swapE τd` for a local duality `τd`. Level
`a` lists its free `A`-slots (the freed sets of `a → a + 1, a + 2, a + 3`) and its free `B`-slots (the images from
`a - 1, a - 2, a - 3`); hub `v` holds position `tA v a` of level `a`, hub `u` position `tB u a`. The hub graph is given
by neighbour lists with the layered bit sets of `BitBFS`. `main7`: a bipartite graph of maximum degree `p + 4` and
diameter at most `7` on `7 (|P| + |L|) + KB + KA` vertices. -/

namespace BipartiteDD.LeanAll.Relax7

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.HexArith BipartiteDD.LeanAll.Orbit2
open BipartiteDD.LeanAll.HexLocal BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.TypedHex BipartiteDD.LeanAll.TypedHex5
open BipartiteDD.LeanAll.RTyped BipartiteDD.LeanAll.BitBFS
open SimpleGraph Finset
open scoped Classical

set_option linter.unusedSectionVars false

/-! ## Lists -/

theorem card_getD_inj_le {α : Type*} (l : List α) (d : α) {K : ℕ} (f : Fin K → ℕ) (hf : Function.Injective f)
    (hlt : ∀ v, f v < l.length) (x : α) :
    (univ.filter (fun v : Fin K => l.getD (f v) d = x)).card ≤ cnt x l := by
  letI := Classical.decEq α
  have h : (univ.filter (fun i : Fin l.length => List.Vector.get (⟨l, rfl⟩ : List.Vector α l.length) i = x)).card =
      l.count x := Fin.card_filter_univ_eq_vector_get_eq_count x (⟨l, rfl⟩ : List.Vector α l.length)
  rw [← count_eq_cnt, ← h]
  refine Finset.card_le_card_of_injOn (fun v => (⟨f v, hlt v⟩ : Fin l.length)) (fun v hv => ?_)
    (fun v _ w _ h => hf (by simpa using congrArg Fin.val h))
  have hv' := (Finset.mem_filter.1 hv).2
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
  rw [List.getD_eq_getElem _ _ (hlt v)] at hv'
  simpa [List.Vector.get] using hv'

theorem icc13 (P : ℕ → Prop) :
    ((Finset.Icc 1 3).filter P).card = (if P 1 then 1 else 0) + (if P 2 then 1 else 0) + (if P 3 then 1 else 0) := by
  have e : Finset.Icc 1 3 = {1, 2, 3} := by decide
  rw [e, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton]
  by_cases h1 : P 1 <;> by_cases h2 : P 2 <;> by_cases h3 : P 3 <;> simp [h1, h2, h3]

theorem count_le_three {α : Type*} {l1 l2 l3 : List α} (h1 : l1.Nodup) (h2 : l2.Nodup) (h3 : l3.Nodup) (x : α)
    {P : ℕ → Prop} (hA : x ∈ l1 → P 1) (hB : x ∈ l2 → P 2) (hC : x ∈ l3 → P 3) :
    cnt x (l1 ++ l2 ++ l3) ≤ ((Finset.Icc 1 3).filter P).card := by
  rw [cnt_append, cnt_append, icc13]
  have key : ∀ (k : ℕ) (l : List α), l.Nodup → (x ∈ l → P k) → cnt x l ≤ (if P k then 1 else 0) := by
    intro k l hl hP
    by_cases h : P k
    · rw [if_pos h]; exact cnt_le_one x hl
    · rw [if_neg h, cnt_zero (fun hx => h (hP hx))]
  have := key 1 l1 h1 hA; have := key 2 l2 h2 hB; have := key 3 l3 h3 hC
  omega

theorem getD_app3 {α : Type*} {n1 n2 n3 : ℕ} {f1 f2 f3 : ℕ → α} (d : α) {i : ℕ} (hi : i < n1 + n2 + n3) :
    ((List.range n1).map f1 ++ (List.range n2).map f2 ++ (List.range n3).map f3).getD i d =
      if i < n1 then f1 i else if i < n1 + n2 then f2 (i - n1) else f3 (i - n1 - n2) := by
  rw [List.getD_eq_getElem _ _ (by simp; omega)]
  by_cases h1 : i < n1
  · rw [if_pos h1, List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
    simp
  · rw [if_neg h1]
    by_cases h2 : i < n1 + n2
    · rw [if_pos h2, List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
      simp
    · rw [if_neg h2, List.getElem_append_right (by simp; omega)]
      simp
      congr 1
      omega

/-! ## Elements by code -/

variable {p : ℕ} [Fact p.Prime]

/-- The point of code `c.1` (`b = false`) or the line of basis `c` (`b = true`). -/
noncomputable def den (p : ℕ) [Fact p.Prime] (b : Bool) (c : ℕ × ℕ) : SPt (ZMod p) ⊕ HLine (ZMod p) :=
  cond b (.inr (lineOf p c.1 c.2)) (.inl (ptOf p c.1))

@[simp] theorem colE_den (b : Bool) (c : ℕ × ℕ) : colE (den p b c) = b := by cases b <;> rfl

/-- A valid code. -/
def CodeOK (p : ℕ) [Fact p.Prime] (b : Bool) (c : ℕ × ℕ) : Prop := cond b (LnOK p c.1 c.2) (PtOK p c.1)

/-- Incidence of the element `(b, c)` and the element `(!b, c')`, with coefficients `α, β`. -/
def adjC (p : ℕ) (b : Bool) (c c' : ℕ × ℕ) (α β : ℕ) : Bool :=
  cond b (linN p c'.1 c.1 c.2 α β) (linN p c.1 c'.1 c'.2 α β)

theorem adj_den {b : Bool} {c c' : ℕ × ℕ} {α β : ℕ} (h : CodeOK p b c) (h' : CodeOK p (!b) c')
    (ha : adjC p b c c' α β = true) : (Hexagon.incGraph hexInc).Adj (den p b c) (den p (!b) c') := by
  cases b
  · simp only [CodeOK, Bool.cond_false, Bool.not_false, Bool.cond_true, adjC] at h h' ha
    exact Hexagon.incGraph_adj_inl_inr.2 (inc_of_lin h h' ha)
  · simp only [CodeOK, Bool.cond_true, Bool.not_true, Bool.cond_false, adjC] at h h' ha
    exact Hexagon.incGraph_adj_inr_inl.2 (inc_of_lin h' h ha)

/-- The list of `n` elements of kind `b` and codes `cd`. -/
noncomputable def lst (p : ℕ) [Fact p.Prime] (n : ℕ) (b : Bool) (cd : ℕ → ℕ × ℕ) :
    List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
  (List.range n).map (fun t => den p b (cd t))

theorem mem_lst {n : ℕ} {b : Bool} {cd : ℕ → ℕ × ℕ} {x : SPt (ZMod p) ⊕ HLine (ZMod p)} :
    x ∈ lst p n b cd ↔ ∃ t < n, den p b (cd t) = x := by
  simp [lst, List.mem_map, List.mem_range]

theorem colE_of_lst {n : ℕ} {b : Bool} {cd : ℕ → ℕ × ℕ} {x : SPt (ZMod p) ⊕ HLine (ZMod p)} (h : x ∈ lst p n b cd) :
    colE x = b := by
  obtain ⟨t, -, rfl⟩ := mem_lst.1 h; exact colE_den b _

@[simp] theorem length_lst (n : ℕ) (b : Bool) (cd : ℕ → ℕ × ℕ) : (lst p n b cd).length = n := by simp [lst]

/-! ## Levels -/

/-- Transition `a → a + k` (`1 ≤ k ≤ 3`). -/
def trn (a k : ℕ) : ℕ := 3 * a + (k - 1)

/-- The source level of the transition into level `a` of length `k`. -/
def src (a k : ℕ) : ℕ := (a + 7 - k) % 7

theorem src_add {a k : ℕ} (ha : a < 7) (hk : k ≤ 3) : src ((a + k) % 7) k = a := by
  unfold src; omega

theorem add_src {a k : ℕ} (ha : a < 7) (hk : k ≤ 3) : (src a k + k) % 7 = a := by
  unfold src; omega

theorem val_add7 (i : ZMod (2 * 3 + 1)) (k : ℕ) : (i + (k : ZMod (2 * 3 + 1))).val = (i.val + k) % 7 := by
  rw [ZMod.val_add, ZMod.val_natCast]; show (i.val + k % 7) % 7 = (i.val + k) % 7; omega

theorem val_sub7 (i : ZMod (2 * 3 + 1)) {k : ℕ} (hk : k ≤ 3) : (i - (k : ZMod (2 * 3 + 1))).val = src i.val k := by
  have e : i - (k : ZMod (2 * 3 + 1)) = i + ((7 - k : ℕ) : ZMod (2 * 3 + 1)) := by
    rw [sub_eq_add_neg]
    congr 1
    rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_add, Nat.sub_add_cancel (by omega)]
    rfl
  rw [e, val_add7]; unfold src
  have := i.isLt; show (i.val + (7 - k)) % 7 = (i.val + 7 - k) % 7; omega

theorem val_lt7 (i : ZMod (2 * 3 + 1)) : i.val < 7 := i.isLt

theorem eq_of_val7 {i i' : ZMod (2 * 3 + 1)} (h : i.val = i'.val) : i = i' := Fin.ext h

/-! ## The construction -/

section Defs

variable (p) (TY : ℕ → Bool) (τd : SPt (ZMod p) ≃ HLine (ZMod p)) (nT : ℕ → ℕ) (kF kI : ℕ → Bool)
  (cF cI : ℕ → ℕ → ℕ × ℕ)

/-- The default element. -/
noncomputable def dE : SPt (ZMod p) ⊕ HLine (ZMod p) := den p false (0, 0)

/-- The freed set of transition `tr`. -/
noncomputable def FL (tr : ℕ) : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := lst p (nT tr) (kF tr) (cF tr)

/-- The images of the freed set of transition `tr`. -/
noncomputable def IL (tr : ℕ) : List (SPt (ZMod p) ⊕ HLine (ZMod p)) := lst p (nT tr) (kI tr) (cI tr)

/-- The free `A`-slots of level `a`. -/
noncomputable def Al (a : ℕ) : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
  FL p nT kF cF (trn a 1) ++ FL p nT kF cF (trn a 2) ++ FL p nT kF cF (trn a 3)

/-- The free `B`-slots of level `a`. -/
noncomputable def Bl (a : ℕ) : List (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
  IL p nT kI cI (trn (src a 1) 1) ++ IL p nT kI cI (trn (src a 2) 2) ++ IL p nT kI cI (trn (src a 3) 3)

/-- The matching of transition `a → a + k`, on naturals. -/
noncomputable def sgN (a k : ℕ) : (SPt (ZMod p) ⊕ HLine (ZMod p)) ≃ (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
  if TY a = TY ((a + k) % 7) then swapE τd else Equiv.refl _

/-- The matchings. -/
noncomputable def sg7 (i : ZMod (2 * 3 + 1)) (k : ℕ) : (SPt (ZMod p) ⊕ HLine (ZMod p)) ≃ (SPt (ZMod p) ⊕ HLine (ZMod p)) :=
  sgN p TY τd i.val k

/-- The freed sets. -/
def R7 (i : ZMod (2 * 3 + 1)) (k : ℕ) : Set (SPt (ZMod p) ⊕ HLine (ZMod p)) := {x | x ∈ FL p nT kF cF (trn i.val k)}

/-- The `A`-slot of hub `v` at level `i`. -/
noncomputable def slV {KB : ℕ} (tA : ℕ → ℕ → ℕ) (v : Fin KB) (i : ZMod (2 * 3 + 1)) : SPt (ZMod p) ⊕ HLine (ZMod p) :=
  (Al p nT kF cF i.val).getD (tA v.val i.val) (dE p)

/-- The `B`-slot of hub `u` at level `i`. -/
noncomputable def slU {KA : ℕ} (tB : ℕ → ℕ → ℕ) (u : Fin KA) (i : ZMod (2 * 3 + 1)) : SPt (ZMod p) ⊕ HLine (ZMod p) :=
  (Bl p nT kI cI i.val).getD (tB u.val i.val) (dE p)

end Defs

/-- The hub graph from neighbour lists. -/
def NS7 {KB KA : ℕ} (nbV : ℕ → List ℕ) (v : Fin KB) (u : Fin KA) : Prop := u.val ∈ nbV v.val

theorem hub_adj {KB KA : ℕ} {nbV : ℕ → List ℕ} {v : Fin KB} {u : Fin KA} (h : NS7 nbV v u) :
    (hubGraph (NS7 nbV)).Adj (.inl v) (.inr u) :=
  (SimpleGraph.fromRel_adj _ _ _).2 ⟨Sum.inl_ne_inr, Or.inl h⟩

theorem card_filter_mem_le {K : ℕ} (l : List ℕ) : (univ.filter (fun u : Fin K => u.val ∈ l)).card ≤ l.length := by
  refine le_trans (Finset.card_le_card_of_injOn (fun u => u.val) (t := l.toFinset) (fun u hu => ?_)
    (fun u _ w _ h => Fin.ext h)) (List.toFinset_card_le l)
  simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hu
  simpa using hu

theorem base3_hex (hp : 2 ≤ p) : Base3 (hexInc (F := ZMod p)) := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  refine ⟨base_hex, fun a => ?_, fun l => ?_⟩
  · have hP : (univ.filter (hexInc a)).card = p + 1 := by
      rw [← card_lns a, Nat.card_eq_fintype_card, Fintype.card_subtype]
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < (univ.filter (hexInc a)).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
    exact ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩
  · have hL : (univ.filter (fun y => hexInc y l)).card = p + 1 := by
      rw [← card_pts l, Nat.card_eq_fintype_card, Fintype.card_subtype]
    obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
      Finset.two_lt_card_iff.1 (by omega : 2 < (univ.filter (fun y => hexInc y l)).card)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy hz
    exact ⟨x, y, z, hxy, hxz, hyz, hx, hy, hz⟩

/-! ## The theorem -/

theorem bool_ne {a b : Bool} (h : a ≠ b) : a = !b := by cases a <;> cases b <;> simp_all

/-- **Seven typed levels over `H(p)` with relaxed friendly sets.** -/
theorem main7 (p : ℕ) [Fact p.Prime] (hp : 3 ≤ p) (TY : ℕ → Bool) (τd : SPt (ZMod p) ≃ HLine (ZMod p))
    (nT : ℕ → ℕ) (kF kI : ℕ → Bool) (cF cI : ℕ → ℕ → ℕ × ℕ) (pr : ℕ → ℕ → ℕ)
    (hkF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kF (trn a k) = TY a)
    (hkI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → kI (trn a k) = !TY ((a + k) % 7))
    (hnF : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → (FL p nT kF cF (trn a k)).Nodup)
    (hnI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → (IL p nT kI cI (trn a k)).Nodup)
    (hfr : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a ≠ TY ((a + k) % 7) → IL p nT kI cI (trn a k) = FL p nT kF cF (trn a k))
    (hsw : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a = TY ((a + k) % 7) → ∀ t < nT (trn a k),
      swapE τd (den p (kF (trn a k)) (cF (trn a k) t)) = den p (kI (trn a k)) (cI (trn a k) t))
    (hr2 : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a = TY ((a + k) % 7) → ∀ t < nT (trn a k), ∀ x,
      Co hexInc (den p (kF (trn a k)) (cF (trn a k) t)) x ↔
        Co hexInc (swapE τd (den p (kF (trn a k)) (cF (trn a k) t))) (swapE τd x))
    (hpr : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ r < nT (trn a k), ∀ s < nT (trn a k),
      Co hexInc (den p (kF (trn a k)) (cF (trn a k) r)) (den p (kF (trn a k)) (cF (trn a k) s)) → s = pr (trn a k) r)
    (hprN : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a = TY ((a + k) % 7) → ∀ r < nT (trn a k), pr (trn a k) r = r)
    (KB KA : ℕ) (tA tB iA iB : ℕ → ℕ → ℕ)
    (htA : ∀ a < 7, ∀ v < KB, tA v a < (Al p nT kF cF a).length ∧ iA a (tA v a) = v)
    (htB : ∀ a < 7, ∀ u < KA, tB u a < (Bl p nT kI cI a).length ∧ iB a (tB u a) = u)
    (hh : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → TY a ≠ TY ((a + k) % 7) → ∀ r < nT (trn a k), pr (trn a k) r ≠ r →
      (∃ u < KA, (Bl p nT kI cI ((a + k) % 7)).getD (tB u ((a + k) % 7)) (dE p) = den p (kF (trn a k)) (cF (trn a k) r) ∧
        (Hexagon.incGraph hexInc).Adj ((Bl p nT kI cI a).getD (tB u a) (dE p))
          (den p (kF (trn a k)) (cF (trn a k) (pr (trn a k) r)))) ∧
      (∃ v < KB, (Al p nT kF cF a).getD (tA v a) (dE p) = den p (kF (trn a k)) (cF (trn a k) r) ∧
        (Hexagon.incGraph hexInc).Adj ((Al p nT kF cF ((a + k) % 7)).getD (tA v ((a + k) % 7)) (dE p))
          (den p (kF (trn a k)) (cF (trn a k) (pr (trn a k) r)))))
    (nbV nbU : ℕ → List ℕ)
    (hV : ∀ x < KB, ∀ y ∈ nbV x, y < KA ∧ x ∈ nbU y) (hU : ∀ y < KA, ∀ x ∈ nbU y, x < KB ∧ y ∈ nbV x)
    (hdV : ∀ x < KB, (nbV x).length ≤ p - 3) (hdU : ∀ y < KA, (nbU y).length ≤ p - 3)
    (V2 V3 V4 V5 U2 U3 U4 U5 : ℕ → ℕ)
    (hV2 : ∀ x < KB, layOK V2 (fun y => orL unit (nbU y)) nbV x = true)
    (hV3 : ∀ y < KA, layOK V3 V2 nbU y = true) (hV4 : ∀ x < KB, layOK V4 V3 nbV x = true)
    (hV5 : ∀ y < KA, layOK V5 V4 nbU y = true) (hV6 : ∀ x < KB, finOK KB V5 nbV x = true)
    (hU2 : ∀ y < KA, layOK U2 (fun x => orL unit (nbV x)) nbU y = true)
    (hU3 : ∀ x < KB, layOK U3 U2 nbV x = true) (hU4 : ∀ y < KA, layOK U4 U3 nbU y = true)
    (hU5 : ∀ x < KB, layOK U5 U4 nbV x = true) (hU6 : ∀ y < KA, finOK KA U5 nbU y = true) :
    ∃ G : SimpleGraph (Fin (7 * (2 * ((p + 1) * (1 + p ^ 2 + p ^ 4))) + KB + KA)), IsBipartiteDegDiam G (p + 4) 7 := by
  letI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  letI : Fintype (HLine (ZMod p)) := Fintype.ofFinite _
  -- membership
  have memFL : ∀ tr x, x ∈ FL p nT kF cF tr ↔ ∃ t < nT tr, den p (kF tr) (cF tr t) = x := fun tr x => mem_lst
  have memIL : ∀ tr x, x ∈ IL p nT kI cI tr ↔ ∃ t < nT tr, den p (kI tr) (cI tr t) = x := fun tr x => mem_lst
  -- images of the matchings
  have imI : ∀ a < 7, ∀ k, 1 ≤ k → k ≤ 3 → ∀ y ∈ IL p nT kI cI (trn a k),
      (sgN p TY τd a k).symm y ∈ FL p nT kF cF (trn a k) := by
    intro a ha k hk1 hk3 y hy
    unfold sgN
    split_ifs with h
    · obtain ⟨t, ht, rfl⟩ := (memIL _ y).1 hy
      rw [← hsw a ha k hk1 hk3 h t ht, Equiv.symm_apply_apply]
      exact (memFL _ _).2 ⟨t, ht, rfl⟩
    · rw [Equiv.refl_symm, Equiv.refl_apply, ← hfr a ha k hk1 hk3 h]; exact hy
  -- the hypotheses of RTyped
  have hmaps : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ x, colE x = TY i.val →
      colE (sg7 p TY τd i k x) = !TY (i + (k : ZMod (2 * 3 + 1))).val := by
    intro i k hk1 hk3 x hx
    rw [val_add7]; unfold sg7 sgN
    split_ifs with h
    · rw [colE_swap, hx, h]
    · rw [Equiv.refl_apply, hx]; exact bool_ne h
  have honto : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ y, colE y = !TY (i + (k : ZMod (2 * 3 + 1))).val →
      colE ((sg7 p TY τd i k).symm y) = TY i.val := by
    intro i k hk1 hk3 y hy
    rw [val_add7] at hy; unfold sg7 sgN
    split_ifs with h
    · rw [colE_swap_symm, hy, h, Bool.not_not]
    · rw [Equiv.refl_symm, Equiv.refl_apply, hy]; exact (bool_ne h).symm
  have hrA : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ x ∈ R7 p nT kF cF i k, colE x = TY i.val := by
    intro i k hk1 hk3 x hx
    rw [colE_of_lst hx, hkF _ (val_lt7 i) k hk1 hk3]
  have hr1 : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ r ∈ R7 p nT kF cF i k, ∀ s ∈ R7 p nT kF cF i k,
      ∀ s' ∈ R7 p nT kF cF i k, Co hexInc r s → Co hexInc r s' → s = s' := by
    intro i k hk1 hk3 r hr s hs s' hs' h1 h2
    obtain ⟨t, ht, rfl⟩ := (memFL _ r).1 hr
    obtain ⟨t1, ht1, rfl⟩ := (memFL _ s).1 hs
    obtain ⟨t2, ht2, rfl⟩ := (memFL _ s').1 hs'
    rw [hpr _ (val_lt7 i) k hk1 hk3 t ht t1 ht1 h1, hpr _ (val_lt7 i) k hk1 hk3 t ht t2 ht2 h2]
  have hr1h : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ r ∈ R7 p nT kF cF i k, ∀ s ∈ R7 p nT kF cF i k, Co hexInc r s →
      (∃ u : Fin KA, slU p nT kI cI tB u (i + (k : ZMod (2 * 3 + 1))) = sg7 p TY τd i k r ∧
        (Hexagon.incGraph hexInc).Adj (slU p nT kI cI tB u i) s) ∧
      (∃ v : Fin KB, slV p nT kF cF tA v i = r ∧
        (Hexagon.incGraph hexInc).Adj (slV p nT kF cF tA v (i + (k : ZMod (2 * 3 + 1)))) (sg7 p TY τd i k s)) := by
    intro i k hk1 hk3 r hr s hs hco
    obtain ⟨t, ht, rfl⟩ := (memFL _ r).1 hr
    obtain ⟨t1, ht1, rfl⟩ := (memFL _ s).1 hs
    have ha := val_lt7 i
    have e1 := hpr _ ha k hk1 hk3 t ht t1 ht1 hco
    subst e1
    have hne : pr (trn i.val k) t ≠ t := fun h => hco.1 (by rw [h])
    have hfr' : TY i.val ≠ TY ((i.val + k) % 7) := fun h => hne (hprN _ ha k hk1 hk3 h t ht)
    have hσ : sg7 p TY τd i k = Equiv.refl _ := by unfold sg7 sgN; rw [if_neg hfr']
    obtain ⟨⟨u, hu, hu1, hu2⟩, ⟨v, hv, hv1, hv2⟩⟩ := hh _ ha k hk1 hk3 hfr' t ht hne
    refine ⟨⟨⟨u, hu⟩, ?_, ?_⟩, ⟨⟨v, hv⟩, ?_, ?_⟩⟩
    · rw [hσ, Equiv.refl_apply]; unfold slU; rw [val_add7]; exact hu1
    · exact hu2
    · exact hv1
    · rw [hσ, Equiv.refl_apply]; unfold slV; rw [val_add7]; exact hv2
  have hr2' : ∀ i (k : ℕ), 1 ≤ k → k ≤ 3 → ∀ r ∈ R7 p nT kF cF i k, ∀ x,
      Co hexInc r x ↔ Co hexInc (sg7 p TY τd i k r) (sg7 p TY τd i k x) := by
    intro i k hk1 hk3 r hr x
    unfold sg7 sgN
    split_ifs with h
    · obtain ⟨t, ht, rfl⟩ := (memFL _ r).1 hr
      exact hr2 _ (val_lt7 i) k hk1 hk3 h t ht x
    · exact Iff.rfl
  have hmemA : ∀ (v : Fin KB) i, slV p nT kF cF tA v i ∈ Al p nT kF cF i.val := by
    intro v i
    unfold slV
    rw [List.getD_eq_getElem _ _ (htA _ (val_lt7 i) _ v.isLt).1]
    exact List.getElem_mem _
  have hmemB : ∀ (u : Fin KA) i, slU p nT kI cI tB u i ∈ Bl p nT kI cI i.val := by
    intro u i
    unfold slU
    rw [List.getD_eq_getElem _ _ (htB _ (val_lt7 i) _ u.isLt).1]
    exact List.getElem_mem _
  have hslotA : ∀ (v : Fin KB) i, colE (slV p nT kF cF tA v i) = TY i.val := by
    intro v i
    have hm := hmemA v i
    have ha := val_lt7 i
    unfold Al at hm
    rcases List.mem_append.1 hm with hm | hm
    · rcases List.mem_append.1 hm with hm | hm
      · rw [colE_of_lst hm, hkF _ ha 1 (by omega) (by omega)]
      · rw [colE_of_lst hm, hkF _ ha 2 (by omega) (by omega)]
    · rw [colE_of_lst hm, hkF _ ha 3 (by omega) (by omega)]
  have hslotB : ∀ (u : Fin KA) i, colE (slU p nT kI cI tB u i) = !TY i.val := by
    intro u i
    have hm := hmemB u i
    have ha := val_lt7 i
    have key : ∀ k, 1 ≤ k → k ≤ 3 → kI (trn (src i.val k) k) = !TY i.val := by
      intro k hk1 hk3
      rw [hkI _ (by unfold src; omega) k hk1 hk3, add_src ha hk3]
    unfold Bl at hm
    rcases List.mem_append.1 hm with hm | hm
    · rcases List.mem_append.1 hm with hm | hm
      · rw [colE_of_lst hm, key 1 (by omega) (by omega)]
      · rw [colE_of_lst hm, key 2 (by omega) (by omega)]
    · rw [colE_of_lst hm, key 3 (by omega) (by omega)]
  -- the hub graph
  have hVV : ∀ v v' : Fin KB, Reach (hubGraph (NS7 (KB := KB) (KA := KA) nbV)) (.inl v) (.inl v') 6 := by
    refine reach6 (G := hubGraph (NS7 (KA := KA) nbV)) (vS := fun v : Fin KB => (.inl v : Fin KB ⊕ Fin KA)) (fun u : Fin KA => (.inr u : Fin KB ⊕ Fin KA)) nbV nbU ?_ ?_
      V2 V3 V4 V5 hV2 hV3 hV4 hV5 hV6
    · intro x hx y hy
      exact ⟨(hV x hx y hy).1, (hub_adj (u := ⟨y, (hV x hx y hy).1⟩) (v := ⟨x, hx⟩) hy).symm⟩
    · intro y hy x hx
      obtain ⟨hxK, hyx⟩ := hU y hy x hx
      exact ⟨hxK, hub_adj (v := ⟨x, hxK⟩) (u := ⟨y, hy⟩) hyx⟩
  have hUU : ∀ u u' : Fin KA, Reach (hubGraph (NS7 (KB := KB) (KA := KA) nbV)) (.inr u) (.inr u') 6 := by
    refine reach6 (G := hubGraph (NS7 (KA := KA) nbV)) (vS := fun u : Fin KA => (.inr u : Fin KB ⊕ Fin KA)) (fun v : Fin KB => (.inl v : Fin KB ⊕ Fin KA)) nbU nbV ?_ ?_
      U2 U3 U4 U5 hU2 hU3 hU4 hU5 hU6
    · intro y hy x hx
      obtain ⟨hxK, hyx⟩ := hU y hy x hx
      exact ⟨hxK, hub_adj (v := ⟨x, hxK⟩) (u := ⟨y, hy⟩) hyx⟩
    · intro x hx y hy
      exact ⟨(hV x hx y hy).1, (hub_adj (u := ⟨y, (hV x hx y hy).1⟩) (v := ⟨x, hx⟩) hy).symm⟩
  have H : RTHyp hexInc 3 (fun i => TY i.val) (sg7 p TY τd) (R7 p nT kF cF) (slV p nT kF cF tA (KB := KB))
      (slU p nT kI cI tB (KA := KA)) (NS7 nbV) :=
    ⟨base3_hex (by omega), hmaps, honto, hrA, hr1, hr1h, hr2', hslotA, hslotB, fun v v' => Or.inr (hVV v v'),
      fun u u' => Or.inr (hUU u u')⟩
  have hSV : ∀ i x, (univ.filter (fun v : Fin KB => slV p nT kF cF tA v i = x)).card ≤
      ((Finset.Icc 1 3).filter (fun k => x ∈ R7 p nT kF cF i k)).card := by
    intro i x
    have ha := val_lt7 i
    have hinj : Function.Injective (fun v : Fin KB => tA v.val i.val) := by
      intro v w h
      have e1 := (htA _ ha _ v.isLt).2
      have e2 := (htA _ ha _ w.isLt).2
      simp only at h
      rw [h] at e1
      exact Fin.ext (e1.symm.trans e2)
    have h1 : (univ.filter (fun v : Fin KB => slV p nT kF cF tA v i = x)).card ≤ cnt x (Al p nT kF cF i.val) := by
      unfold slV
      convert card_getD_inj_le (Al p nT kF cF i.val) (dE p) (fun v : Fin KB => tA v.val i.val) hinj
        (fun v => (htA _ ha _ v.isLt).1) x
    refine le_trans h1 ?_
    exact count_le_three (hnF _ ha 1 (by omega) (by omega)) (hnF _ ha 2 (by omega) (by omega))
      (hnF _ ha 3 (by omega) (by omega)) x id id id
  have hSU : ∀ i y, (univ.filter (fun u : Fin KA => slU p nT kI cI tB u i = y)).card ≤
      ((Finset.Icc 1 3).filter (fun k : ℕ => (sg7 p TY τd (i - (k : ZMod (2 * 3 + 1))) k).symm y ∈
        R7 p nT kF cF (i - (k : ZMod (2 * 3 + 1))) k)).card := by
    intro i y
    have ha := val_lt7 i
    have hinj : Function.Injective (fun u : Fin KA => tB u.val i.val) := by
      intro v w h
      have e1 := (htB _ ha _ v.isLt).2
      have e2 := (htB _ ha _ w.isLt).2
      simp only at h
      rw [h] at e1
      exact Fin.ext (e1.symm.trans e2)
    have h1 : (univ.filter (fun u : Fin KA => slU p nT kI cI tB u i = y)).card ≤ cnt y (Bl p nT kI cI i.val) := by
      unfold slU
      convert card_getD_inj_le (Bl p nT kI cI i.val) (dE p) (fun u : Fin KA => tB u.val i.val) hinj
        (fun u => (htB _ ha _ u.isLt).1) y
    refine le_trans h1 ?_
    have key : ∀ k, 1 ≤ k → k ≤ 3 → y ∈ IL p nT kI cI (trn (src i.val k) k) →
        (sg7 p TY τd (i - (k : ZMod (2 * 3 + 1))) k).symm y ∈ R7 p nT kF cF (i - (k : ZMod (2 * 3 + 1))) k := by
      intro k hk1 hk3 hy
      unfold sg7 R7
      rw [val_sub7 i hk3]
      exact imI _ (by unfold src; omega) k hk1 hk3 y hy
    have hs : ∀ k, src i.val k < 7 := fun k => by unfold src; omega
    exact count_le_three (hnI _ (hs 1) 1 (by omega) (by omega)) (hnI _ (hs 2) 2 (by omega) (by omega))
      (hnI _ (hs 3) 3 (by omega) (by omega)) y (key 1 (by omega) (by omega)) (key 2 (by omega) (by omega))
      (key 3 (by omega) (by omega))
  have hNV : ∀ v : Fin KB, (univ.filter (NS7 (KA := KA) nbV v)).card ≤ p - 3 :=
    fun v => le_trans (by unfold NS7; convert card_filter_mem_le (K := KA) (nbV v.val)) (hdV _ v.isLt)
  have hNU : ∀ u : Fin KA, (univ.filter (fun v : Fin KB => NS7 nbV v u)).card ≤ p - 3 := by
    intro u
    refine le_trans (Finset.card_le_card (fun v hv => ?_))
      (le_trans (card_filter_mem_le (K := KB) (nbU u.val)) (hdU _ u.isLt))
    have hv' := (Finset.mem_filter.1 hv).2
    unfold NS7 at hv'
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (hV _ v.isLt _ hv').2⟩
  have main := H.exists_graph (q := p) (fun x => deg_E x) (fun i x => by convert hSV i x)
    (fun i y => by convert hSU i y) (fun v => by convert hNV v) (fun u => by convert hNU u) hp
  have hcP : Fintype.card (SPt (ZMod p)) = (p + 1) * (1 + p ^ 2 + p ^ 4) := by
    rw [← Nat.card_eq_fintype_card, card_spt_eq, ZMod.card]
  have hcL : Fintype.card (HLine (ZMod p)) = Fintype.card (SPt (ZMod p)) := by
    have := card_lines_eq (inc := hexInc (F := ZMod p)) (k := p + 1) (by omega) (fun x => card_lns x)
      (fun W => card_pts W)
    rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this
  have e : (2 * 3 + 1) * (Fintype.card (SPt (ZMod p)) + Fintype.card (HLine (ZMod p))) + Fintype.card (Fin KB) +
      Fintype.card (Fin KA) = 7 * (2 * ((p + 1) * (1 + p ^ 2 + p ^ 4))) + KB + KA := by
    rw [hcL, hcP, Fintype.card_fin, Fintype.card_fin]; ring
  rw [e, show p + 1 + 3 = p + 4 by ring] at main
  exact main

end BipartiteDD.LeanAll.Relax7
