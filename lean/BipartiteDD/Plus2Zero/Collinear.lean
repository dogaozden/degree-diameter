import BipartiteDD.Plus2Zero.Basic

/-! Any two distinct points of the zero-change structure lie on a common line
(`prop:zero`, the "two points" step). Old pairs are joined in the plane; the new points are
joined through the copies. -/

namespace BipartiteDD.Plus2Zero
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

namespace Frame
variable (F : Frame P L)

/-- Two distinct plane points: their plane line. -/
theorem pp (u v : P) (huv : u ≠ v) : ∃ x : L ⊕ NewLn, F.inc (.inl u) x ∧ F.inc (.inl v) x := by
  obtain ⟨m, hum, hvm⟩ := line_through (L := L) huv
  exact ⟨.inl m, (F.inc_pp _ _).2 hum, (F.inc_pp _ _).2 hvm⟩

/-- `Q` and a plane point. -/
theorem Q_pt (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr .Q) x ∧ F.inc (.inl u) x := by
  by_cases hA : u = F.A
  · subst hA
    refine ⟨.inl (F.AX .a), (F.inc_Ql _).2 ⟨F.A_mem_AX .a, F.AX_ne (by decide),
      F.AX_ne (by decide), F.AX_ne (by decide)⟩, (F.inc_pp _ _).2 (F.A_mem_AX .a)⟩
  · obtain ⟨m, hAm, hum⟩ := line_through (L := L) (Ne.symm hA)
    by_cases h1 : m = F.AX .one
    · subst h1
      by_cases hu : u = F.X .one
      · subst hu
        exact ⟨.inr (.K .two), F.inc_QK _, (F.inc_pK2 _).2 (Or.inr rfl)⟩
      · exact ⟨.inr (.K .one), F.inc_QK _, (F.inc_pK1 _).2 (Or.inl ⟨hum, hA, hu⟩)⟩
    by_cases h2 : m = F.AX .two
    · subst h2
      by_cases hu : u = F.X .two
      · subst hu
        exact ⟨.inr (.K .three), F.inc_QK _, (F.inc_pK3 _).2 (Or.inr rfl)⟩
      · exact ⟨.inr (.K .two), F.inc_QK _, (F.inc_pK2 _).2 (Or.inl ⟨hum, hA, hu⟩)⟩
    by_cases h3 : m = F.AX .three
    · subst h3
      by_cases hu : u = F.X .three
      · subst hu
        exact ⟨.inr (.K .one), F.inc_QK _, (F.inc_pK1 _).2 (Or.inr rfl)⟩
      · exact ⟨.inr (.K .three), F.inc_QK _, (F.inc_pK3 _).2 (Or.inl ⟨hum, hA, hu⟩)⟩
    · exact ⟨.inl m, (F.inc_Ql m).2 ⟨hAm, h1, h2, h3⟩, (F.inc_pp _ _).2 hum⟩

/-- `H a` and a plane point. -/
theorem Ha_pt (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr (.H .a)) x ∧ F.inc (.inl u) x := by
  by_cases hu : u = F.X .a
  · subst hu
    exact ⟨.inr .M, F.inc_HM _, (F.inc_pM _).2 ⟨F.X_mem .a, F.X_ne (by decide),
      F.X_ne (by decide), F.X_ne (by decide)⟩⟩
  · obtain ⟨m, hXm, hum⟩ := line_through (L := L) (Ne.symm hu)
    by_cases h1 : m = F.AX .a
    · subst h1
      exact ⟨.inr (.K .a), (F.inc_HK _ _).2 rfl, (F.inc_pKa _).2 ⟨hum, hu⟩⟩
    · exact ⟨.inl m, (F.inc_Ha _).2 ⟨hXm, h1⟩, (F.inc_pp _ _).2 hum⟩

/-- `H one` and a plane point. -/
theorem H1_pt (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr (.H .one)) x ∧ F.inc (.inl u) x := by
  by_cases hu : u = F.X .one
  · subst hu
    obtain ⟨m, hXm, hmℓ, hmA⟩ := BipartiteDD.Plus2.exists_line_ne (F.X .one) F.ell (F.AX .one)
    exact ⟨.inl m, (F.inc_H1 _).2 (Or.inl ⟨hXm, hmℓ, hmA⟩), (F.inc_pp _ _).2 hXm⟩
  · obtain ⟨m, hXm, hum⟩ := line_through (L := L) (Ne.symm hu)
    by_cases h1 : m = F.ell
    · subst h1
      by_cases h2 : u = F.X .two
      · subst h2
        exact ⟨.inl (F.AX .two), (F.inc_H1 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.X_mem_AX .two)⟩
      by_cases h3 : u = F.X .three
      · subst h3
        exact ⟨.inr (.K .one), (F.inc_HK _ _).2 rfl, (F.inc_pK1 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .M, F.inc_HM _, (F.inc_pM _).2 ⟨hum, hu, h2, h3⟩⟩
    by_cases h2 : m = F.AX .one
    · subst h2
      by_cases h3 : u = F.A
      · subst h3
        exact ⟨.inl (F.AX .two), (F.inc_H1 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.A_mem_AX .two)⟩
      · exact ⟨.inr (.K .one), (F.inc_HK _ _).2 rfl, (F.inc_pK1 _).2 (Or.inl ⟨hum, h3, hu⟩)⟩
    · exact ⟨.inl m, (F.inc_H1 _).2 (Or.inl ⟨hXm, h1, h2⟩), (F.inc_pp _ _).2 hum⟩

/-- `H two` and a plane point. -/
theorem H2_pt (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr (.H .two)) x ∧ F.inc (.inl u) x := by
  by_cases hu : u = F.X .two
  · subst hu
    obtain ⟨m, hXm, hmℓ, hmA⟩ := BipartiteDD.Plus2.exists_line_ne (F.X .two) F.ell (F.AX .two)
    exact ⟨.inl m, (F.inc_H2 _).2 (Or.inl ⟨hXm, hmℓ, hmA⟩), (F.inc_pp _ _).2 hXm⟩
  · obtain ⟨m, hXm, hum⟩ := line_through (L := L) (Ne.symm hu)
    by_cases h1 : m = F.ell
    · subst h1
      by_cases h2 : u = F.X .three
      · subst h2
        exact ⟨.inl (F.AX .three), (F.inc_H2 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.X_mem_AX .three)⟩
      by_cases h3 : u = F.X .one
      · subst h3
        exact ⟨.inr (.K .two), (F.inc_HK _ _).2 rfl, (F.inc_pK2 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .M, F.inc_HM _, (F.inc_pM _).2 ⟨hum, h3, hu, h2⟩⟩
    by_cases h2 : m = F.AX .two
    · subst h2
      by_cases h3 : u = F.A
      · subst h3
        exact ⟨.inl (F.AX .three), (F.inc_H2 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.A_mem_AX .three)⟩
      · exact ⟨.inr (.K .two), (F.inc_HK _ _).2 rfl, (F.inc_pK2 _).2 (Or.inl ⟨hum, h3, hu⟩)⟩
    · exact ⟨.inl m, (F.inc_H2 _).2 (Or.inl ⟨hXm, h1, h2⟩), (F.inc_pp _ _).2 hum⟩

/-- `H three` and a plane point. -/
theorem H3_pt (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr (.H .three)) x ∧ F.inc (.inl u) x := by
  by_cases hu : u = F.X .three
  · subst hu
    obtain ⟨m, hXm, hmℓ, hmA⟩ := BipartiteDD.Plus2.exists_line_ne (F.X .three) F.ell (F.AX .three)
    exact ⟨.inl m, (F.inc_H3 _).2 (Or.inl ⟨hXm, hmℓ, hmA⟩), (F.inc_pp _ _).2 hXm⟩
  · obtain ⟨m, hXm, hum⟩ := line_through (L := L) (Ne.symm hu)
    by_cases h1 : m = F.ell
    · subst h1
      by_cases h2 : u = F.X .one
      · subst h2
        exact ⟨.inl (F.AX .one), (F.inc_H3 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.X_mem_AX .one)⟩
      by_cases h3 : u = F.X .two
      · subst h3
        exact ⟨.inr (.K .three), (F.inc_HK _ _).2 rfl, (F.inc_pK3 _).2 (Or.inr rfl)⟩
      exact ⟨.inr .M, F.inc_HM _, (F.inc_pM _).2 ⟨hum, h2, h3, hu⟩⟩
    by_cases h2 : m = F.AX .three
    · subst h2
      by_cases h3 : u = F.A
      · subst h3
        exact ⟨.inl (F.AX .one), (F.inc_H3 _).2 (Or.inr rfl), (F.inc_pp _ _).2 (F.A_mem_AX .one)⟩
      · exact ⟨.inr (.K .three), (F.inc_HK _ _).2 rfl, (F.inc_pK3 _).2 (Or.inl ⟨hum, h3, hu⟩)⟩
    · exact ⟨.inl m, (F.inc_H3 _).2 (Or.inl ⟨hXm, h1, h2⟩), (F.inc_pp _ _).2 hum⟩

/-- A new point (`Q` or some `H h`) and a plane point have a common line. -/
theorem newpt_pt (q : NewPt) (u : P) : ∃ x : L ⊕ NewLn, F.inc (.inr q) x ∧ F.inc (.inl u) x := by
  rcases q with _ | h
  · exact F.Q_pt u
  · rcases h with _ | _ | _ | _
    · exact F.Ha_pt u
    · exact F.H1_pt u
    · exact F.H2_pt u
    · exact F.H3_pt u

/-- Any two distinct points of the new structure lie on a common line. -/
theorem pts (u v : P ⊕ NewPt) (huv : u ≠ v) :
    ∃ x : L ⊕ NewLn, F.inc u x ∧ F.inc v x := by
  rcases u with p | q <;> rcases v with p' | q'
  · exact F.pp p p' (fun e => huv (congrArg Sum.inl e))
  · obtain ⟨x, h1, h2⟩ := F.newpt_pt q' p
    exact ⟨x, h2, h1⟩
  · exact F.newpt_pt q p'
  · rcases q with _ | h <;> rcases q' with _ | k
    · exact absurd rfl huv
    · exact ⟨.inr (.K k), F.inc_QK k, (F.inc_HK k k).2 rfl⟩
    · exact ⟨.inr (.K h), (F.inc_HK h h).2 rfl, F.inc_QK h⟩
    · exact ⟨.inr .M, F.inc_HM h, F.inc_HM k⟩

end Frame

end BipartiteDD.Plus2Zero
