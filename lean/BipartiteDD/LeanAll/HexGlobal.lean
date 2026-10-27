import BipartiteDD.LeanAll.Spread
import BipartiteDD.LeanAll.HexGen
import BipartiteDD.LeanAll.VHub

/-! # Whole hexagons from tables: a duality and a freed spread (the (11,7) construction)

A table of all `N` points (codes `pc`, increasing) and all `N` lines (bases `la, lb`, Plücker codes increasing) of
`H(q)` over a field with a `HexGen.Coder` gives equivalences `Fin N ≃ SPt F`, `Fin N ≃ HLine F` (injective by the
order, onto by counting). A duality is given by permutations `dP` (point `i` to line `dP i`) and `dL` (line `j` to
point `dL j`): each line `j` lists its `q + 1` points `e` with coefficients, and for each the coefficients of the dual
point `dL j` on the dual line `dP e`. By counting (`q + 1` points on a line, `q + 1` lines through a point) the lists
are complete, so incidence is preserved both ways (`dual_iff`). Flags `fP` (freed points) and `fL` (spread lines),
with the spread line `sl i` of each freed point: a flagged line has only freed points, all with `sl = j`; an
unflagged line has at most one freed point. That is `Spread.SpreadLike` (`spread_of`). With a voltage hub graph
(`VHub`) whose hubs sit on the freed points listed by `fpt`, `main` is `Spread.exists_graph`. -/

namespace BipartiteDD.LeanAll.HexGlobal

open BipartiteDD BipartiteDD.Hexagon BipartiteDD.HexagonD7 BipartiteDD.LeanAll.Orbit2 BipartiteDD.LeanAll.HexLocal
open BipartiteDD.LeanAll.HexGen BipartiteDD.LeanAll.Typed BipartiteDD.LeanAll.Spread BipartiteDD.LeanAll.VHub
open SimpleGraph Finset
open scoped Classical

set_option linter.unusedSectionVars false

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem base_hexF : Base (hexInc (F := F)) := by
  have hG := HexagonEven.genPolygonGraph_hexagon_even (F := F)
  exact ⟨pl_of_polygon hG, p2_of_polygon hG, l2_of_polygon hG⟩

/-- Entry `i` of the point table. -/
def gptOK (C : Coder F) (N : ℕ) (pc dP dPi sl : ℕ → ℕ) (fP fL : ℕ → Bool)
    (ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (i : ℕ) : Bool :=
  C.ptB (pc i) && (Nat.beq (i + 1) N || Nat.blt (pc i) (pc (i + 1))) && Nat.blt (dP i) N &&
    Nat.beq (dPi (dP i)) i &&
    (!(fP i) || (Nat.blt (sl i) N && fL (sl i) && (ents (sl i)).any (fun t => Nat.beq t.1 i)))

/-- Entry `j` of the line table. -/
def glnOK (C : Coder F) (q N : ℕ) (pc la lb dP dL dLi sl : ℕ → ℕ) (fP fL : ℕ → Bool)
    (ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) (j : ℕ) : Bool :=
  C.lnB (la j) (lb j) && (Nat.beq (j + 1) N || Nat.blt (C.plC (la j) (lb j)) (C.plC (la (j + 1)) (lb (j + 1)))) &&
    Nat.blt (dL j) N && Nat.beq (dLi (dL j)) j &&
    Nat.beq (lenP (ents j)) (q + 1) && sortedLt ((ents j).map (·.1)) &&
    allP (fun t => Nat.blt t.1 N && C.lin (pc t.1) (la j) (lb j) t.2.1 t.2.2.1 &&
      C.lin (pc (dL j)) (la (dP t.1)) (lb (dP t.1)) t.2.2.2.1 t.2.2.2.2) (ents j) &&
    cond (fL j) (allP (fun t => fP t.1 && Nat.beq (sl t.1) j) (ents j))
      (Nat.ble (lenP ((ents j).filter (fun t => fP t.1))) 1)

theorem len_le_one {α : Type*} {l : List α} (h : l.length ≤ 1) {a b : α} (ha : a ∈ l) (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [x], _, ha, hb => simp only [List.mem_singleton] at ha hb; rw [ha, hb]

section Tables

variable {C : Coder F} {q N : ℕ} {pc la lb dP dPi dL dLi sl : ℕ → ℕ} {fP fL : ℕ → Bool}
  {ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)}

/-- What the table checks give. -/
structure TabOK (C : Coder F) (q N : ℕ) (pc la lb dP dPi dL dLi sl : ℕ → ℕ) (fP fL : ℕ → Bool)
    (ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)) : Prop where
  hq : Fintype.card F = q
  hNP : Nat.card (SPt F) = N
  hNL : Nat.card (HLine F) = N
  pt : ∀ i < N, gptOK C N pc dP dPi sl fP fL ents i = true
  ln : ∀ j < N, glnOK C q N pc la lb dP dL dLi sl fP fL ents j = true

variable (T : TabOK C q N pc la lb dP dPi dL dLi sl fP fL ents)
include T

theorem TabOK.ptB {i : ℕ} (hi : i < N) : C.ptB (pc i) = true := by
  have := T.pt i hi; simp only [gptOK, Bool.and_eq_true] at this; exact this.1.1.1.1

theorem TabOK.lnB {j : ℕ} (hj : j < N) : C.lnB (la j) (lb j) = true := by
  have := T.ln j hj; simp only [glnOK, Bool.and_eq_true] at this; exact this.1.1.1.1.1.1.1

theorem TabOK.dP_lt {i : ℕ} (hi : i < N) : dP i < N := by
  have := T.pt i hi; simp only [gptOK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1.1.2

theorem TabOK.dPi_dP {i : ℕ} (hi : i < N) : dPi (dP i) = i := by
  have := T.pt i hi; simp only [gptOK, Bool.and_eq_true, Nat.beq_eq] at this; exact this.1.2

theorem TabOK.dL_lt {j : ℕ} (hj : j < N) : dL j < N := by
  have := T.ln j hj; simp only [glnOK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1.1.1.1.1.2

theorem TabOK.dLi_dL {j : ℕ} (hj : j < N) : dLi (dL j) = j := by
  have := T.ln j hj; simp only [glnOK, Bool.and_eq_true, Nat.beq_eq] at this; exact this.1.1.1.1.2

theorem TabOK.len {j : ℕ} (hj : j < N) : (ents j).length = q + 1 := by
  have := T.ln j hj; simp only [glnOK, Bool.and_eq_true, Nat.beq_eq, lenP_eq] at this; exact this.1.1.1.2

theorem TabOK.sorted {j : ℕ} (hj : j < N) : sortedLt ((ents j).map (·.1)) = true := by
  have := T.ln j hj; simp only [glnOK, Bool.and_eq_true] at this; exact this.1.1.2

theorem TabOK.ent {j : ℕ} (hj : j < N) : ∀ t ∈ ents j, t.1 < N ∧ C.lin (pc t.1) (la j) (lb j) t.2.1 t.2.2.1 = true ∧
    C.lin (pc (dL j)) (la (dP t.1)) (lb (dP t.1)) t.2.2.2.1 t.2.2.2.2 = true := by
  have := T.ln j hj
  simp only [glnOK, Bool.and_eq_true, allP_eq, List.all_eq_true, Nat.blt_eq] at this
  intro t ht
  obtain ⟨⟨h1, h2⟩, h3⟩ := this.1.2 t ht
  exact ⟨h1, h2, h3⟩

theorem TabOK.flagL {j : ℕ} (hj : j < N) (hf : fL j = true) : ∀ t ∈ ents j, fP t.1 = true ∧ sl t.1 = j := by
  have := T.ln j hj
  simp only [glnOK, Bool.and_eq_true, hf, cond_true, allP_eq, List.all_eq_true, Nat.beq_eq] at this
  exact this.2

theorem TabOK.unflagL {j : ℕ} (hj : j < N) (hf : fL j = false) :
    ((ents j).filter (fun t => fP t.1)).length ≤ 1 := by
  have := T.ln j hj
  simp only [glnOK, Bool.and_eq_true, hf, cond_false, Nat.ble_eq, lenP_eq] at this
  exact this.2

theorem TabOK.flagP {i : ℕ} (hi : i < N) (hf : fP i = true) :
    sl i < N ∧ fL (sl i) = true ∧ ∃ t ∈ ents (sl i), t.1 = i := by
  have := T.pt i hi
  simp only [gptOK, Bool.and_eq_true, hf, Bool.not_true, Bool.false_or, Nat.blt_eq, List.any_eq_true,
    Nat.beq_eq] at this
  exact ⟨this.2.1.1, this.2.1.2, this.2.2⟩

/-- The point of index `i`. -/
noncomputable def P_ (C : Coder F) (pc : ℕ → ℕ) (i : ℕ) : SPt F := HexGen.ptOf C (pc i)

/-- The line of index `j`. -/
noncomputable def L_ (C : Coder F) (la lb : ℕ → ℕ) (j : ℕ) : HLine F := HexGen.lineOf C (la j) (lb j)

theorem TabOK.P_inj {i i' : ℕ} (hi : i < N) (hi' : i' < N) (h : P_ C pc i = P_ C pc i') : i = i' := by
  have hinc : ∀ i, i + 1 < N → pc i < pc (i + 1) := by
    intro i hi
    have := T.pt i (by omega); simp only [gptOK, Bool.and_eq_true] at this
    exact ltOfBlt (succ_of this.1.1.1.2 hi)
  exact inj_of_succ hinc i hi i' hi' (HexGen.ptOf_inj (T.ptB hi) (T.ptB hi') h)

theorem TabOK.lninc {j : ℕ} (hj : j + 1 < N) : C.plC (la j) (lb j) < C.plC (la (j + 1)) (lb (j + 1)) := by
  have h := T.ln j (by omega)
  unfold glnOK at h
  have h2 : (Nat.beq (j + 1) N || Nat.blt (C.plC (la j) (lb j)) (C.plC (la (j + 1)) (lb (j + 1)))) = true := by
    revert h; generalize (Nat.beq (j + 1) N || Nat.blt (C.plC (la j) (lb j)) (C.plC (la (j + 1)) (lb (j + 1)))) = b
    cases b <;> simp
  exact ltOfBlt (succ_of h2 hj)

theorem TabOK.L_inj {j j' : ℕ} (hj : j < N) (hj' : j' < N) (h : L_ C la lb j = L_ C la lb j') : j = j' := by
  have hinc : ∀ j, j + 1 < N → C.plC (la j) (lb j) < C.plC (la (j + 1)) (lb (j + 1)) := fun j hj => T.lninc hj
  exact inj_of_succ (f := fun j => C.plC (la j) (lb j)) hinc j hj j' hj' (HexGen.lineOf_inj (T.lnB hj) (T.lnB hj') h)

/-- The points, as an equivalence. -/
noncomputable def TabOK.ptE : Fin N ≃ SPt F :=
  Equiv.ofBijective (fun i => P_ C pc i.val)
    (Function.Injective.bijective_of_nat_card_le (fun i i' h => Fin.ext (T.P_inj i.isLt i'.isLt h))
      (by rw [T.hNP, Nat.card_eq_fintype_card, Fintype.card_fin]))

/-- The lines, as an equivalence. -/
noncomputable def TabOK.lnE : Fin N ≃ HLine F :=
  Equiv.ofBijective (fun j => L_ C la lb j.val)
    (Function.Injective.bijective_of_nat_card_le (fun j j' h => Fin.ext (T.L_inj j.isLt j'.isLt h))
      (by rw [T.hNL, Nat.card_eq_fintype_card, Fintype.card_fin]))

theorem TabOK.ptE_apply (i : Fin N) : T.ptE i = P_ C pc i.val := rfl
theorem TabOK.lnE_apply (j : Fin N) : T.lnE j = L_ C la lb j.val := rfl

/-- `dP` as a permutation. -/
noncomputable def TabOK.dPe : Fin N ≃ Fin N :=
  Equiv.ofBijective (fun i => ⟨dP i.val, T.dP_lt i.isLt⟩)
    (Finite.injective_iff_bijective.1 fun i i' h => Fin.ext (by
      have := congrArg (fun x : Fin N => dPi x.val) h
      simp only [T.dPi_dP i.isLt, T.dPi_dP i'.isLt] at this
      exact this))

/-- `dL` as a permutation. -/
noncomputable def TabOK.dLe : Fin N ≃ Fin N :=
  Equiv.ofBijective (fun j => ⟨dL j.val, T.dL_lt j.isLt⟩)
    (Finite.injective_iff_bijective.1 fun j j' h => Fin.ext (by
      have := congrArg (fun x : Fin N => dLi x.val) h
      simp only [T.dLi_dL j.isLt, T.dLi_dL j'.isLt] at this
      exact this))

/-- The duality on points. -/
noncomputable def TabOK.φP : SPt F ≃ HLine F := T.ptE.symm.trans (T.dPe.trans T.lnE)

/-- The duality on lines. -/
noncomputable def TabOK.φL : HLine F ≃ SPt F := T.lnE.symm.trans (T.dLe.trans T.ptE)

theorem TabOK.φP_ptE (i : Fin N) : T.φP (T.ptE i) = L_ C la lb (dP i.val) := by
  simp [TabOK.φP, TabOK.dPe, TabOK.lnE_apply]

theorem TabOK.φL_lnE (j : Fin N) : T.φL (T.lnE j) = P_ C pc (dL j.val) := by
  simp [TabOK.φL, TabOK.dLe, TabOK.ptE_apply]

/-- The listed points of line `j` are all its points. -/
theorem TabOK.pts_of {j : ℕ} (hj : j < N) (x : SPt F) (hx : hexInc x (L_ C la lb j)) :
    ∃ t ∈ ents j, x = P_ C pc t.1 := by
  have hmem : x ∈ (ents j).map (fun t => P_ C pc t.1) := by
    refine mem_of_card (card_pts' (L_ C la lb j)) _ (by rw [List.length_map, T.len hj, T.hq]) ?_ ?_ x hx
    · exact nodup_map_of (nodup_of_sortedLt (T.sorted hj)) (fun t ht t' ht' htt =>
        T.P_inj (T.ent hj t ht).1 (T.ent hj t' ht').1 htt)
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
      exact HexGen.inc_of_lin (T.ptB (T.ent hj t ht).1) (T.lnB hj) (T.ent hj t ht).2.1
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
  exact ⟨t, ht, rfl⟩

/-- The dual lines of the points of line `j` are all lines through its dual point. -/
theorem TabOK.lns_of {j : ℕ} (hj : j < N) (W : HLine F) (hW : hexInc (P_ C pc (dL j)) W) :
    ∃ t ∈ ents j, W = L_ C la lb (dP t.1) := by
  have hmem : W ∈ (ents j).map (fun t => L_ C la lb (dP t.1)) := by
    refine mem_of_card (card_lns' (P_ C pc (dL j))) _ (by rw [List.length_map, T.len hj, T.hq]) ?_ ?_ W hW
    · refine nodup_map_of (nodup_of_sortedLt (T.sorted hj)) (fun t ht t' ht' htt => ?_)
      have h1 := (T.ent hj t ht).1
      have h2 := (T.ent hj t' ht').1
      have := T.L_inj (T.dP_lt h1) (T.dP_lt h2) htt
      rw [← T.dPi_dP h1, ← T.dPi_dP h2, this]
    · intro y hy
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hy
      exact HexGen.inc_of_lin (T.ptB (T.dL_lt hj)) (T.lnB (T.dP_lt (T.ent hj t ht).1)) (T.ent hj t ht).2.2
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hmem
  exact ⟨t, ht, rfl⟩

/-- **The duality.** -/
theorem TabOK.dual_iff (x : SPt F) (W : HLine F) : hexInc x W ↔ hexInc (T.φL W) (T.φP x) := by
  obtain ⟨i, rfl⟩ := T.ptE.surjective x
  obtain ⟨j, rfl⟩ := T.lnE.surjective W
  rw [T.φP_ptE, T.φL_lnE, T.ptE_apply, T.lnE_apply]
  constructor
  · intro h
    obtain ⟨t, ht, he⟩ := T.pts_of j.isLt _ h
    have hti := T.P_inj i.isLt (T.ent j.isLt t ht).1 he
    have := HexGen.inc_of_lin (T.ptB (T.dL_lt j.isLt)) (T.lnB (T.dP_lt (T.ent j.isLt t ht).1)) (T.ent j.isLt t ht).2.2
    rwa [← hti] at this
  · intro h
    obtain ⟨t, ht, he⟩ := T.lns_of j.isLt _ h
    have h1 := (T.ent j.isLt t ht).1
    have hti : i.val = t.1 := by
      have := T.L_inj (T.dP_lt i.isLt) (T.dP_lt h1) he
      rw [← T.dPi_dP i.isLt, ← T.dPi_dP h1, this]
    rw [hti]
    exact HexGen.inc_of_lin (T.ptB h1) (T.lnB j.isLt) (T.ent j.isLt t ht).2.1

/-- The freed points. -/
def TabOK.Fr : Set (SPt F) := {x | fP (T.ptE.symm x).val = true}

theorem TabOK.mem_Fr (i : Fin N) : T.ptE i ∈ T.Fr ↔ fP i.val = true := by
  simp [TabOK.Fr]

/-- **The spread.** -/
theorem TabOK.spread_of : SpreadLike (hexInc (F := F)) T.Fr := by
  intro u hu
  obtain ⟨i, rfl⟩ := T.ptE.surjective u
  have hfi := (T.mem_Fr i).1 hu
  obtain ⟨hsl, hfl, t0, ht0, ht0i⟩ := T.flagP i.isLt hfi
  refine ⟨L_ C la lb (sl i.val), ?_, fun M hM hMℓ x hx hxu hxF => ?_⟩
  · have := HexGen.inc_of_lin (T.ptB (T.ent hsl t0 ht0).1) (T.lnB hsl) (T.ent hsl t0 ht0).2.1
    rw [ht0i] at this
    rw [T.ptE_apply]; exact this
  · obtain ⟨j, rfl⟩ := T.lnE.surjective M
    obtain ⟨k, rfl⟩ := T.ptE.surjective x
    rw [T.lnE_apply] at hM hMℓ hx
    rw [T.ptE_apply] at hM hx hxu
    have hfk := (T.mem_Fr k).1 hxF
    obtain ⟨ti, hti, ei⟩ := T.pts_of j.isLt _ hM
    obtain ⟨tk, htk, ek⟩ := T.pts_of j.isLt _ hx
    have ei' := T.P_inj i.isLt (T.ent j.isLt ti hti).1 ei
    have ek' := T.P_inj k.isLt (T.ent j.isLt tk htk).1 ek
    cases hf : fL j.val
    · have h1 : ti ∈ (ents j.val).filter (fun t => fP t.1) := List.mem_filter.2 ⟨hti, by rw [← ei']; exact hfi⟩
      have h2 : tk ∈ (ents j.val).filter (fun t => fP t.1) := List.mem_filter.2 ⟨htk, by rw [← ek']; exact hfk⟩
      have := len_le_one (T.unflagL j.isLt hf) h1 h2
      apply hxu
      rw [ek', ← this, ← ei']; rfl
    · have := (T.flagL j.isLt hf ti hti).2
      rw [← ei'] at this
      exact hMℓ (by rw [this])

end Tables

/-! ## The theorem -/

/-- Entry `v` of the list of hub owners (increasing, freed). -/
def gfOK (N K : ℕ) (fpt : ℕ → ℕ) (fP : ℕ → Bool) (v : ℕ) : Bool :=
  Nat.blt (fpt v) N && fP (fpt v) && (Nat.beq (v + 1) K || Nat.blt (fpt v) (fpt (v + 1)))

theorem deg_inc [Fintype (SPt F)] [Fintype (HLine F)] {q : ℕ} (hq : Fintype.card F = q) (x : SPt F ⊕ HLine F) :
    (univ.filter ((Hexagon.incGraph (hexInc (F := F))).Adj x)).card ≤ q + 1 := by
  rcases x with a | l
  · have hP : (univ.filter (hexInc a)).card = q + 1 := by
      rw [← hq, ← card_lns' a, Nat.card_eq_fintype_card, Fintype.card_subtype]
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
  · have hL : (univ.filter (fun y => hexInc y l)).card = q + 1 := by
      rw [← hq, ← card_pts' l, Nat.card_eq_fintype_card, Fintype.card_subtype]
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

/-- **Freed spread with a duality, from tables.** `2j + 1` levels of `H(q)`, the duality of the tables as every
matching, the flagged points freed, and `K = b m` hubs of each kind on the freed points `fpt v` with a voltage hub
graph: a bipartite graph of maximum degree `q + 1 + j` and diameter at most `7` on `(2j + 1) · 2N + 2K` vertices. -/
theorem main {C : Coder F} {q N : ℕ} {pc la lb dP dPi dL dLi sl : ℕ → ℕ} {fP fL : ℕ → Bool}
    {ents : ℕ → List (ℕ × ℕ × ℕ × ℕ × ℕ)} (T : TabOK C q N pc la lb dP dPi dL dLi sl fP fL ents)
    (j vm vb : ℕ) (E : List (ℕ × ℕ × ℕ)) (hb : 0 < vb) (fpt : ℕ → ℕ)
    (hF : ∀ v < vb * vm, gfOK N (vb * vm) fpt fP v = true)
    (hHL : LocalSpec (q - j) (2 * (vb * vm)) (vnb vm vb E) (vcol vb))
    (hHD : (graphF (2 * (vb * vm)) (vnb vm vb E)).ediam ≤ 7) (hj1 : 1 ≤ j) (hjq : j ≤ q) :
    ∃ G : SimpleGraph (Fin ((2 * j + 1) * (N + N) + vb * vm + vb * vm)), IsBipartiteDegDiam G (q + 1 + j) 7 := by
  letI : Fintype (SPt F) := Fintype.ofFinite _
  letI : Fintype (HLine F) := Fintype.ofFinite _
  have hf1 : ∀ v < vb * vm, fpt v < N ∧ fP (fpt v) = true := fun v hv => by
    have := hF v hv; simp only [gfOK, Bool.and_eq_true, Nat.blt_eq] at this; exact this.1
  have hinc : ∀ v, v + 1 < vb * vm → fpt v < fpt (v + 1) := fun v hv => by
    have := hF v (by omega); simp only [gfOK, Bool.and_eq_true] at this; exact ltOfBlt (succ_of this.2 hv)
  let own : Fin (vb * vm) → ZMod (2 * j + 1) → SPt F := fun v _ => T.ptE ⟨fpt v.val, (hf1 v.val v.isLt).1⟩
  have hown : ∀ i (x : SPt F), (univ.filter (fun v => own v i = x)).card ≤ j := by
    intro i x
    refine le_trans (Finset.card_le_one.2 fun v hv w hw => ?_) hj1
    simp only [mem_filter, mem_univ, true_and] at hv hw
    have h := T.ptE.injective (hv.trans hw.symm)
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (inj_of_succ hinc v.val v.isLt w.val w.isLt h)
  have hFr : ∀ v i, own v i ∈ T.Fr := fun v i => (T.mem_Fr _).2 (hf1 v.val v.isLt).2
  obtain ⟨hV, hU, hNV, hNU⟩ := vhub (d := q - j) hb hHL hHD
  have := Spread.exists_graph (q := q) (j := j) (V := Fin (vb * vm)) (U := Fin (vb * vm)) (base_hexF (F := F))
    T.spread_of T.dual_iff (fun x => deg_inc T.hq x) own own (vNS vm vb E) hFr hFr
    (fun i x => by convert hown i x) (fun i x => by convert hown i x) hV hU hNV hNU hjq
  obtain ⟨G, hG⟩ := this
  have e : (2 * j + 1) * (Fintype.card (SPt F) + Fintype.card (HLine F)) + Fintype.card (Fin (vb * vm)) +
      Fintype.card (Fin (vb * vm)) = (2 * j + 1) * (N + N) + vb * vm + vb * vm := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, T.hNP, T.hNL, Fintype.card_fin]
  exact ⟨_, BipartiteDD.isBipartiteDegDiam_comap (finCongr e) hG⟩

end BipartiteDD.LeanAll.HexGlobal
