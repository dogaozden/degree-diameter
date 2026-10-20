import BipartiteDD.Plus2Zero.Defs
import BipartiteDD.Plus2.Basic

/-! Basic facts about the zero-change frame: unfolding lemmas for `Frame.inc`, and the lines
`AX h` through `A` and the feet `X h`. -/

namespace BipartiteDD.Plus2Zero
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

/-- Two distinct points lie on a common line. -/
theorem line_through {p q : P} (h : p ≠ q) : ∃ m : L, p ∈ m ∧ q ∈ m :=
  ⟨_, (HasLines.mkLine_ax h).1, (HasLines.mkLine_ax h).2⟩

/-- Two distinct lines meet in a point. -/
theorem inter_pt {l m : L} (h : l ≠ m) : ∃ y : P, y ∈ l ∧ y ∈ m :=
  ⟨_, (HasPoints.mkPoint_ax (P := P) h).1, (HasPoints.mkPoint_ax (P := P) h).2⟩

namespace Frame

variable (F : Frame P L)

/-! ### Unfolding lemmas for `inc` -/

theorem inc_pp (u : P) (l : L) : F.inc (.inl u) (.inl l) ↔ u ∈ l :=
  Iff.rfl

theorem inc_pM (u : P) : F.inc (.inl u) (.inr .M) ↔
    (u ∈ F.ell ∧ u ≠ F.X .one ∧ u ≠ F.X .two ∧ u ≠ F.X .three) :=
  Iff.rfl

theorem inc_pKa (u : P) : F.inc (.inl u) (.inr (.K .a)) ↔ (u ∈ F.AX .a ∧ u ≠ F.X .a) :=
  Iff.rfl

theorem inc_pK1 (u : P) : F.inc (.inl u) (.inr (.K .one)) ↔
    ((u ∈ F.AX .one ∧ u ≠ F.A ∧ u ≠ F.X .one) ∨ u = F.X .three) :=
  Iff.rfl

theorem inc_pK2 (u : P) : F.inc (.inl u) (.inr (.K .two)) ↔
    ((u ∈ F.AX .two ∧ u ≠ F.A ∧ u ≠ F.X .two) ∨ u = F.X .one) :=
  Iff.rfl

theorem inc_pK3 (u : P) : F.inc (.inl u) (.inr (.K .three)) ↔
    ((u ∈ F.AX .three ∧ u ≠ F.A ∧ u ≠ F.X .three) ∨ u = F.X .two) :=
  Iff.rfl

theorem inc_Ql (l : L) : F.inc (.inr .Q) (.inl l) ↔
    (F.A ∈ l ∧ l ≠ F.AX .one ∧ l ≠ F.AX .two ∧ l ≠ F.AX .three) :=
  Iff.rfl

theorem not_inc_QM : ¬ F.inc (.inr .Q) (.inr .M) := fun h => h

theorem inc_QK (k : Hat) : F.inc (.inr .Q) (.inr (.K k)) := trivial

theorem inc_Ha (l : L) : F.inc (.inr (.H .a)) (.inl l) ↔ (F.X .a ∈ l ∧ l ≠ F.AX .a) :=
  Iff.rfl

theorem inc_H1 (l : L) : F.inc (.inr (.H .one)) (.inl l) ↔
    ((F.X .one ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .one) ∨ l = F.AX .two) :=
  Iff.rfl

theorem inc_H2 (l : L) : F.inc (.inr (.H .two)) (.inl l) ↔
    ((F.X .two ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .two) ∨ l = F.AX .three) :=
  Iff.rfl

theorem inc_H3 (l : L) : F.inc (.inr (.H .three)) (.inl l) ↔
    ((F.X .three ∈ l ∧ l ≠ F.ell ∧ l ≠ F.AX .three) ∨ l = F.AX .one) :=
  Iff.rfl

theorem inc_HM (h : Hat) : F.inc (.inr (.H h)) (.inr .M) := by
  cases h <;> trivial

theorem inc_HK (h k : Hat) : F.inc (.inr (.H h)) (.inr (.K k)) ↔ h = k := by
  cases h <;> cases k <;> exact Iff.rfl

/-! ### The lines `AX h` -/

theorem A_mem_AX (h : Hat) : F.A ∈ F.AX h := (HasLines.mkLine_ax (F.A_ne_X h)).1

theorem X_mem_AX (h : Hat) : F.X h ∈ F.AX h := (HasLines.mkLine_ax (F.A_ne_X h)).2

theorem AX_ne_ell (h : Hat) : F.AX h ≠ F.ell := fun e => F.A_not_mem (e ▸ F.A_mem_AX h)

theorem AX_inj : Function.Injective F.AX := by
  intro h k e
  by_contra hk
  have hX : F.X h ≠ F.X k := fun e' => hk (F.X_inj e')
  rcases Nondegenerate.eq_or_eq (F.X_mem h) (F.X_mem k) (F.X_mem_AX h)
      (by rw [e]; exact F.X_mem_AX k) with e' | e'
  · exact hX e'
  · exact F.AX_ne_ell h e'.symm

/-- A point of `ℓ` lies on `AX h` only if it is `X h`. -/
theorem mem_AX_iff (h : Hat) {p : P} (hp : p ∈ F.ell) : p ∈ F.AX h ↔ p = F.X h :=
  ⟨fun e => (Nondegenerate.eq_or_eq hp (F.X_mem h) e (F.X_mem_AX h)).resolve_right
    (fun e' => F.AX_ne_ell h e'.symm),
   fun e => e ▸ F.X_mem_AX h⟩

/-- Two different hat lines meet only in `A`. -/
theorem eq_A_of_mem_AX_AX {h k : Hat} (hhk : h ≠ k) {p : P} (h1 : p ∈ F.AX h)
    (h2 : p ∈ F.AX k) : p = F.A :=
  (Nondegenerate.eq_or_eq h1 (F.A_mem_AX h) h2 (F.A_mem_AX k)).resolve_right
    (fun e => hhk (F.AX_inj e))

/-- A line through `A` and `X h` is `AX h`. -/
theorem eq_AX_of_mem {l : L} (h : Hat) (hA : F.A ∈ l) (hX : F.X h ∈ l) : l = F.AX h :=
  (Nondegenerate.eq_or_eq hA hX (F.A_mem_AX h) (F.X_mem_AX h)).resolve_left (F.A_ne_X h)

theorem X_ne {h k : Hat} (hhk : h ≠ k) : F.X h ≠ F.X k :=
  fun e => hhk (F.X_inj e)

theorem AX_ne {h k : Hat} (hhk : h ≠ k) : F.AX h ≠ F.AX k :=
  fun e => hhk (F.AX_inj e)

end Frame

end BipartiteDD.Plus2Zero
