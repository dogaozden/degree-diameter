import BipartiteDD.Plus2Zero.Collinear

/-! Any two distinct lines of the zero-change structure are concurrent (the dual step). Old pairs
meet in the plane; a copy meets an old line through the point that the copy sees on it. -/

namespace BipartiteDD.Plus2Zero
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

namespace Frame
variable (F : Frame P L)

/-- Two distinct plane lines meet in a plane point. -/
theorem ll_pair (l m : L) (hlm : l ≠ m) :
    ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inl m) := by
  obtain ⟨y, hyl, hym⟩ := inter_pt (P := P) hlm
  exact ⟨.inl y, (F.inc_pp _ _).2 hyl, (F.inc_pp _ _).2 hym⟩

/-- A plane line and `M`. -/
theorem pM (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr .M) := by
  by_cases hl : l = F.ell
  · subst hl
    exact ⟨.inr (.H .a), (F.inc_Ha _).2 ⟨F.X_mem .a, (F.AX_ne_ell .a).symm⟩, F.inc_HM _⟩
  · obtain ⟨y, hyl, hyl'⟩ := inter_pt (P := P) (Ne.symm hl)
    by_cases hy1 : y = F.X .one
    · subst hy1
      by_cases h2 : l = F.AX .one
      · subst h2
        exact ⟨.inr (.H .three), (F.inc_H3 _).2 (Or.inr rfl), F.inc_HM _⟩
      · exact ⟨.inr (.H .one), (F.inc_H1 _).2 (Or.inl ⟨hyl', hl, h2⟩), F.inc_HM _⟩
    by_cases hy2 : y = F.X .two
    · subst hy2
      by_cases h2 : l = F.AX .two
      · subst h2
        exact ⟨.inr (.H .one), (F.inc_H1 _).2 (Or.inr rfl), F.inc_HM _⟩
      · exact ⟨.inr (.H .two), (F.inc_H2 _).2 (Or.inl ⟨hyl', hl, h2⟩), F.inc_HM _⟩
    by_cases hy3 : y = F.X .three
    · subst hy3
      by_cases h2 : l = F.AX .three
      · subst h2
        exact ⟨.inr (.H .two), (F.inc_H2 _).2 (Or.inr rfl), F.inc_HM _⟩
      · exact ⟨.inr (.H .three), (F.inc_H3 _).2 (Or.inl ⟨hyl', hl, h2⟩), F.inc_HM _⟩
    exact ⟨.inl y, (F.inc_pp _ _).2 hyl', (F.inc_pM y).2 ⟨hyl, hy1, hy2, hy3⟩⟩

/-- A plane line and `K a`. -/
theorem pKa (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr (.K .a)) := by
  by_cases hl : l = F.AX .a
  · subst hl
    exact ⟨.inl F.A, (F.inc_pp _ _).2 (F.A_mem_AX .a), (F.inc_pKa _).2 ⟨F.A_mem_AX .a, F.A_ne_X .a⟩⟩
  · obtain ⟨y, hyA, hyl⟩ := inter_pt (P := P) (Ne.symm hl)
    by_cases hy : y = F.X .a
    · subst hy
      exact ⟨.inr (.H .a), (F.inc_Ha _).2 ⟨hyl, hl⟩, (F.inc_HK _ _).2 rfl⟩
    · exact ⟨.inl y, (F.inc_pp _ _).2 hyl, (F.inc_pKa _).2 ⟨hyA, hy⟩⟩

/-- A plane line and `K one`. -/
theorem pK1 (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr (.K .one)) := by
  by_cases hl : l = F.AX .one
  · subst hl
    obtain ⟨p, hpA, hpA1, hpX⟩ := BipartiteDD.Plus2.exists_point_ne (F.AX .one) F.A (F.X .one)
    exact ⟨.inl p, (F.inc_pp _ _).2 hpA, (F.inc_pK1 _).2 (Or.inl ⟨hpA, hpA1, hpX⟩)⟩
  · obtain ⟨y, hy1, hyl⟩ := inter_pt (P := P) (Ne.symm hl)
    by_cases hyA : y = F.A
    · subst hyA
      by_cases h2 : l = F.AX .two
      · subst h2
        exact ⟨.inr (.H .one), (F.inc_H1 _).2 (Or.inr rfl), (F.inc_HK _ _).2 rfl⟩
      by_cases h3 : l = F.AX .three
      · subst h3
        exact ⟨.inl (F.X .three), (F.inc_pp _ _).2 (F.X_mem_AX .three),
          (F.inc_pK1 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .Q, (F.inc_Ql _).2 ⟨hyl, hl, h2, h3⟩, F.inc_QK _⟩
    by_cases hy' : y = F.X .one
    · subst hy'
      by_cases hℓ : l = F.ell
      · subst hℓ
        exact ⟨.inl (F.X .three), (F.inc_pp _ _).2 (F.X_mem .three), (F.inc_pK1 _).2 (Or.inr rfl)⟩
      exact ⟨.inr (.H .one), (F.inc_H1 _).2 (Or.inl ⟨hyl, hℓ, hl⟩), (F.inc_HK _ _).2 rfl⟩
    · exact ⟨.inl y, (F.inc_pp _ _).2 hyl, (F.inc_pK1 _).2 (Or.inl ⟨hy1, hyA, hy'⟩)⟩

/-- A plane line and `K two`. -/
theorem pK2 (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr (.K .two)) := by
  by_cases hl : l = F.AX .two
  · subst hl
    obtain ⟨p, hpA, hpA1, hpX⟩ := BipartiteDD.Plus2.exists_point_ne (F.AX .two) F.A (F.X .two)
    exact ⟨.inl p, (F.inc_pp _ _).2 hpA, (F.inc_pK2 _).2 (Or.inl ⟨hpA, hpA1, hpX⟩)⟩
  · obtain ⟨y, hy2, hyl⟩ := inter_pt (P := P) (Ne.symm hl)
    by_cases hyA : y = F.A
    · subst hyA
      by_cases h2 : l = F.AX .three
      · subst h2
        exact ⟨.inr (.H .two), (F.inc_H2 _).2 (Or.inr rfl), (F.inc_HK _ _).2 rfl⟩
      by_cases h3 : l = F.AX .one
      · subst h3
        exact ⟨.inl (F.X .one), (F.inc_pp _ _).2 (F.X_mem_AX .one),
          (F.inc_pK2 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .Q, (F.inc_Ql _).2 ⟨hyl, h3, hl, h2⟩, F.inc_QK _⟩
    by_cases hy' : y = F.X .two
    · subst hy'
      by_cases hℓ : l = F.ell
      · subst hℓ
        exact ⟨.inl (F.X .one), (F.inc_pp _ _).2 (F.X_mem .one), (F.inc_pK2 _).2 (Or.inr rfl)⟩
      exact ⟨.inr (.H .two), (F.inc_H2 _).2 (Or.inl ⟨hyl, hℓ, hl⟩), (F.inc_HK _ _).2 rfl⟩
    · exact ⟨.inl y, (F.inc_pp _ _).2 hyl, (F.inc_pK2 _).2 (Or.inl ⟨hy2, hyA, hy'⟩)⟩

/-- A plane line and `K three`. -/
theorem pK3 (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr (.K .three)) := by
  by_cases hl : l = F.AX .three
  · subst hl
    obtain ⟨p, hpA, hpA1, hpX⟩ := BipartiteDD.Plus2.exists_point_ne (F.AX .three) F.A (F.X .three)
    exact ⟨.inl p, (F.inc_pp _ _).2 hpA, (F.inc_pK3 _).2 (Or.inl ⟨hpA, hpA1, hpX⟩)⟩
  · obtain ⟨y, hy3, hyl⟩ := inter_pt (P := P) (Ne.symm hl)
    by_cases hyA : y = F.A
    · subst hyA
      by_cases h2 : l = F.AX .one
      · subst h2
        exact ⟨.inr (.H .three), (F.inc_H3 _).2 (Or.inr rfl), (F.inc_HK _ _).2 rfl⟩
      by_cases h3 : l = F.AX .two
      · subst h3
        exact ⟨.inl (F.X .two), (F.inc_pp _ _).2 (F.X_mem_AX .two),
          (F.inc_pK3 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .Q, (F.inc_Ql _).2 ⟨hyl, h2, h3, hl⟩, F.inc_QK _⟩
    by_cases hy' : y = F.X .three
    · subst hy'
      by_cases hℓ : l = F.ell
      · subst hℓ
        exact ⟨.inl (F.X .two), (F.inc_pp _ _).2 (F.X_mem .two), (F.inc_pK3 _).2 (Or.inr rfl)⟩
      exact ⟨.inr (.H .three), (F.inc_H3 _).2 (Or.inl ⟨hyl, hℓ, hl⟩), (F.inc_HK _ _).2 rfl⟩
    · exact ⟨.inl y, (F.inc_pp _ _).2 hyl, (F.inc_pK3 _).2 (Or.inl ⟨hy3, hyA, hy'⟩)⟩

/-- A plane line and a new line. -/
theorem old_new (l : L) (n : NewLn) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr n) := by
  rcases n with _ | h
  · exact F.pM l
  · rcases h with _ | _ | _ | _
    · exact F.pKa l
    · exact F.pK1 l
    · exact F.pK2 l
    · exact F.pK3 l

/-- Any two distinct lines of the new structure are concurrent. -/
theorem lns (x y : L ⊕ NewLn) (hxy : x ≠ y) :
    ∃ p : P ⊕ NewPt, F.inc p x ∧ F.inc p y := by
  rcases x with l | n <;> rcases y with m | n'
  · exact F.ll_pair l m (fun e => hxy (congrArg Sum.inl e))
  · exact F.old_new l n'
  · obtain ⟨p, h1, h2⟩ := F.old_new m n
    exact ⟨p, h2, h1⟩
  · rcases n with _ | h <;> rcases n' with _ | k
    · exact absurd rfl hxy
    · exact ⟨.inr (.H k), F.inc_HM k, (F.inc_HK k k).2 rfl⟩
    · exact ⟨.inr (.H h), (F.inc_HK h h).2 rfl, F.inc_HM h⟩
    · by_cases hhk : h = k
      · subst hhk
        exact absurd rfl hxy
      · exact ⟨.inr .Q, F.inc_QK h, F.inc_QK k⟩

end Frame

end BipartiteDD.Plus2Zero
