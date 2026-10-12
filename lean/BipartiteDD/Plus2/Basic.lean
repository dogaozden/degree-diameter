import BipartiteDD.Plus2.Defs

/-! Group A: basic facts about frames, and unfolding lemmas for `Frame.inc`. -/

namespace BipartiteDD.Plus2
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

/-- A line has a point other than two given points (it has `q + 1 ≥ 3` points). -/
theorem exists_point_ne [Finite P] [Finite L] (l : L) (a b : P) :
    ∃ p, p ∈ l ∧ p ≠ a ∧ p ≠ b := by
  by_contra h
  push Not at h
  have hsub : {p : P | p ∈ l} ⊆ ({a, b} : Set P) := by
    intro p hp
    by_cases hpa : p = a
    · exact Or.inl hpa
    · exact Or.inr (h p hp hpa)
  have h2 := ProjectivePlane.two_lt_pointCount (P := P) (L := L) l
  have h3 : ({p : P | p ∈ l}).ncard ≤ ({a, b} : Set P).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : ({a, b} : Set P).ncard ≤ 2 :=
    (Set.ncard_insert_le a {b}).trans (by simp)
  have h5 : pointCount P l = ({p : P | p ∈ l}).ncard := Nat.card_coe_set_eq _
  omega

/-- A point has a line other than two given lines (it has `q + 1 ≥ 3` lines). -/
theorem exists_line_ne [Finite P] [Finite L] (p : P) (a b : L) :
    ∃ l, p ∈ l ∧ l ≠ a ∧ l ≠ b := by
  by_contra h
  push Not at h
  have hsub : {l : L | p ∈ l} ⊆ ({a, b} : Set L) := by
    intro l hl
    by_cases hla : l = a
    · exact Or.inl hla
    · exact Or.inr (h l hl hla)
  have h2 := ProjectivePlane.two_lt_lineCount (P := P) (L := L) p
  have h3 : ({l : L | p ∈ l}).ncard ≤ ({a, b} : Set L).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : ({a, b} : Set L).ncard ≤ 2 :=
    (Set.ncard_insert_le a {b}).trans (by simp)
  have h5 : lineCount L p = ({l : L | p ∈ l}).ncard := Nat.card_coe_set_eq _
  omega

namespace Frame

variable (F : Frame P L)


/-! ### Unfolding lemmas for `inc` -/

theorem inc_pp (p : P) (l : L) : F.inc (.inl p) (.inl l) ↔
    ((p ∈ l ∧ ¬ ∃ s, p = F.X s ∧ l = F.AX s) ∨ ∃ t s, cyc t s ∧ p = F.X t ∧ l = F.AX s) :=
  Iff.rfl

theorem inc_pM (p : P) : F.inc (.inl p) (.inr .M) ↔
    (p ∈ F.ell ∧ p ≠ F.X .r0 ∧ p ≠ F.X .r1 ∧ p ≠ F.X .rc) :=
  Iff.rfl

theorem inc_pK (p : P) (s : Row) : F.inc (.inl p) (.inr (.K s)) ↔
    ((p ∈ F.AX s ∧ p ≠ F.A) ∨ (s = .ra ∧ p = F.A)) :=
  Iff.rfl

theorem inc_Ql (l : L) : F.inc (.inr .Q) (.inl l) ↔
    (F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc) :=
  Iff.rfl

theorem not_inc_QM : ¬ F.inc (.inr .Q) (.inr .M) := fun h => h

theorem inc_QK (s : Row) : F.inc (.inr .Q) (.inr (.K s)) := trivial

theorem inc_Hl (s : Row) (l : L) : F.inc (.inr (.H s)) (.inl l) ↔
    ((F.X s ∈ l ∧ l ≠ F.ell) ∨ (s = .ra ∧ l = F.ell)) :=
  Iff.rfl

theorem inc_HM (s : Row) : F.inc (.inr (.H s)) (.inr .M) := trivial

theorem inc_HK (s t : Row) : F.inc (.inr (.H s)) (.inr (.K t)) ↔ cyc s t = true :=
  Iff.rfl

/-! ### Basic facts about the lines `AX s` -/

theorem A_mem_AX (s : Row) : F.A ∈ F.AX s := (HasLines.mkLine_ax (F.A_ne_X s)).1

theorem X_mem_AX (s : Row) : F.X s ∈ F.AX s := (HasLines.mkLine_ax (F.A_ne_X s)).2

theorem AX_ne_ell (s : Row) : F.AX s ≠ F.ell := fun h => F.A_not_mem (h ▸ F.A_mem_AX s)

theorem AX_inj : Function.Injective F.AX := by
  intro s t h
  by_contra hst
  have hX : F.X s ≠ F.X t := fun e => hst (F.X_inj e)
  rcases Nondegenerate.eq_or_eq (F.X_mem s) (F.X_mem t) (F.X_mem_AX s)
      (by rw [h]; exact F.X_mem_AX t) with e | e
  · exact hX e
  · exact F.AX_ne_ell s e.symm

theorem mem_AX_iff (s : Row) {p : P} (hp : p ∈ F.ell) : p ∈ F.AX s ↔ p = F.X s :=
  ⟨fun h => (Nondegenerate.eq_or_eq hp (F.X_mem s) h (F.X_mem_AX s)).resolve_right
    (fun e => F.AX_ne_ell s e.symm),
   fun h => h ▸ F.X_mem_AX s⟩

/-- A line through `Y ∈ ℓ` other than `AX s`, when `Y ≠ X s`. -/
theorem ne_AX_of_mem {m : L} {Y : P} (hY : Y ∈ F.ell) (hYm : Y ∈ m) (s : Row)
    (hYs : Y ≠ F.X s) : m ≠ F.AX s :=
  fun h => hYs ((F.mem_AX_iff s hY).1 (h ▸ hYm))

theorem eq_A_of_mem_AX_AX {s t : Row} (hst : s ≠ t) {p : P} (h1 : p ∈ F.AX s)
    (h2 : p ∈ F.AX t) : p = F.A :=
  (Nondegenerate.eq_or_eq h1 (F.A_mem_AX s) h2 (F.A_mem_AX t)).resolve_right
    (fun e => hst (F.AX_inj e))

/-- A line through `A` and `X s` is `AX s`. -/
theorem eq_AX_of_mem {l : L} (s : Row) (hA : F.A ∈ l) (hX : F.X s ∈ l) : l = F.AX s :=
  (Nondegenerate.eq_or_eq hA hX (F.A_mem_AX s) (F.X_mem_AX s)).resolve_left (F.A_ne_X s)

/-- Distinct row indices give distinct points on `ℓ`. -/
theorem X_ne {s t : Row} (h : s ≠ t) : F.X s ≠ F.X t := fun e => h (F.X_inj e)

end Frame

end BipartiteDD.Plus2
