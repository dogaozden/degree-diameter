import BipartiteDD.Plus2.Collinear

/-! Group C: any two distinct lines of the new structure are concurrent.
The report proves this by duality; here each case is proved directly, with the witnesses read
off from the dual dictionary (REPORT.md section 4, Step 3). -/

namespace BipartiteDD.Plus2
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]

/-- In the 3-cycle on `{0, 1, c}`, two distinct rows are related one way or the other. -/
theorem cyc_cases : ∀ t s : Row, t ≠ .ra → s ≠ .ra → t ≠ s → cyc t s = true ∨ cyc s t = true := by
  decide

namespace Frame
variable (F : Frame P L)

/-- A point of `AX s` (with `X s` on `m ≠ AX s`) lying also on the plane line `m`. -/
theorem pt_AX_pair (s : Row) (m : L) (hm : m ≠ F.AX s) (hXm : F.X s ∈ m) :
    ∃ p : P ⊕ NewPt, F.inc p (.inl (F.AX s)) ∧ F.inc p (.inl m) := by
  by_cases hmℓ : m = F.ell
  · subst hmℓ
    cases s
    · exact ⟨.inl (F.X .r1), F.inc_rot rfl,
        F.inc_pl_of (F.X_mem .r1) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
    · exact ⟨.inl (F.X .rc), F.inc_rot rfl,
        F.inc_pl_of (F.X_mem .rc) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
    · exact ⟨.inr (.H .ra), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX .ra, F.AX_ne_ell .ra⟩),
        (F.inc_Hl _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩
    · exact ⟨.inl (F.X .r0), F.inc_rot rfl,
        F.inc_pl_of (F.X_mem .r0) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
  · exact ⟨.inr (.H s), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX s, F.AX_ne_ell s⟩),
      (F.inc_Hl _ _).2 (Or.inl ⟨hXm, hmℓ⟩)⟩

/-- Two distinct plane lines. -/
theorem pp_lines (l m : L) (hlm : l ≠ m) :
    ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inl m) := by
  have h0 := HasPoints.mkPoint_ax (P := P) hlm
  by_cases F1 : ∃ s, HasPoints.mkPoint (P := P) hlm = F.X s ∧ l = F.AX s
  · obtain ⟨s, hps, hls⟩ := F1
    have hXm : F.X s ∈ m := by rw [← hps]; exact h0.2
    obtain ⟨p, h1, h2⟩ := F.pt_AX_pair s m (fun e => hlm (hls.trans e.symm)) hXm
    exact ⟨p, by rw [hls]; exact h1, h2⟩
  · by_cases F2 : ∃ s, HasPoints.mkPoint (P := P) hlm = F.X s ∧ m = F.AX s
    · obtain ⟨s, hps, hms⟩ := F2
      have hXl : F.X s ∈ l := by rw [← hps]; exact h0.1
      obtain ⟨p, h1, h2⟩ := F.pt_AX_pair s l (fun e => hlm (e.trans hms.symm)) hXl
      exact ⟨p, h2, by rw [hms]; exact h1⟩
    · exact ⟨.inl (HasPoints.mkPoint (P := P) hlm), F.inc_pl_of h0.1 (fun s hs hls => F1 ⟨s, hs, hls⟩),
        F.inc_pl_of h0.2 (fun s hs hms => F2 ⟨s, hs, hms⟩)⟩

/-- A plane line and `M`. -/
theorem pM (l : L) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr .M) := by
  by_cases hl : l = F.ell
  · subst hl
    exact ⟨.inr (.H .ra), (F.inc_Hl _ _).2 (Or.inr ⟨rfl, rfl⟩), F.inc_HM _⟩
  · have hxl := HasPoints.mkPoint_ax (P := P) (Ne.symm hl)
    by_cases hX : ∃ s, HasPoints.mkPoint (P := P) (Ne.symm hl) = F.X s
    · obtain ⟨s, hs⟩ := hX
      refine ⟨.inr (.H s), (F.inc_Hl _ _).2 (Or.inl ⟨?_, hl⟩), F.inc_HM s⟩
      rw [← hs]
      exact hxl.2
    · push Not at hX
      refine ⟨.inl (HasPoints.mkPoint (P := P) (Ne.symm hl)), F.inc_pl_of hxl.2 (fun s hs _ => hX s hs),
        (F.inc_pM _).2 ⟨hxl.1, hX .r0, hX .r1, hX .rc⟩⟩

/-- A line through `A` other than `AX t` for `t ∈ {0, 1, c}`, meeting the hat line `K s`. -/
theorem pK_AX (t s : Row) (ht : t ≠ .ra) :
    ∃ p : P ⊕ NewPt, F.inc p (.inl (F.AX t)) ∧ F.inc p (.inr (.K s)) := by
  by_cases hs : s = .ra
  · subst hs
    exact ⟨.inl F.A, F.inc_pl_of (F.A_mem_AX t) (fun u hu _ => F.A_ne_X u hu),
      (F.inc_pK _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩
  by_cases hst : t = s
  · subst hst
    obtain ⟨Y, hY, hYA, hYX⟩ := exists_point_ne (F.AX t) F.A (F.X t)
    refine ⟨.inl Y, F.inc_pl_of hY (fun u hu e => ?_), F.inc_pK_of hY hYA⟩
    have htu : t = u := F.AX_inj e
    subst htu
    exact hYX hu
  · rcases cyc_cases t s ht hs hst with h | h
    · exact ⟨.inr (.H t), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX t, F.AX_ne_ell t⟩),
        (F.inc_HK _ _).2 h⟩
    · exact ⟨.inl (F.X s), F.inc_rot h, F.inc_pK_of (F.X_mem_AX s) (F.A_ne_X s).symm⟩

/-- A plane line and a hat line `K s`. -/
theorem pK (l : L) (s : Row) : ∃ p : P ⊕ NewPt, F.inc p (.inl l) ∧ F.inc p (.inr (.K s)) := by
  by_cases hAl : F.A ∈ l
  · by_cases hQ : l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc
    · exact ⟨.inr .Q, (F.inc_Ql l).2 ⟨hAl, hQ.1, hQ.2.1, hQ.2.2⟩, F.inc_QK s⟩
    · -- then `l = AX t` for some `t ∈ {0, 1, c}`
      have key : ∃ t : Row, t ≠ .ra ∧ l = F.AX t := by
        by_cases h0 : l = F.AX .r0
        · exact ⟨.r0, by decide, h0⟩
        by_cases h1 : l = F.AX .r1
        · exact ⟨.r1, by decide, h1⟩
        · exact ⟨.rc, by decide, by
            by_contra hc
            exact hQ ⟨h0, h1, hc⟩⟩
      obtain ⟨t, ht, hlt⟩ := key
      rw [hlt]
      exact F.pK_AX t s ht
  · have hl : l ≠ F.AX s := fun e => hAl (by rw [e]; exact F.A_mem_AX s)
    obtain ⟨p, hpl, hpA⟩ : ∃ p : P, p ∈ l ∧ p ∈ F.AX s :=
      ⟨_, (HasPoints.mkPoint_ax (P := P) hl).1, (HasPoints.mkPoint_ax (P := P) hl).2⟩
    have hpA' : p ≠ F.A := fun e => hAl (by rw [← e]; exact hpl)
    refine ⟨.inl p, F.inc_pl_of hpl (fun t _ hlt => hAl (by rw [hlt]; exact F.A_mem_AX t)),
      F.inc_pK_of hpA hpA'⟩

/-- `M` and a hat line `K s`. -/
theorem MK (s : Row) : ∃ p : P ⊕ NewPt, F.inc p (.inr .M) ∧ F.inc p (.inr (.K s)) := by
  rcases s with _ | _ | _ | _
  · exact ⟨.inr (.H .r1), F.inc_HM _, (F.inc_HK _ _).2 rfl⟩
  · exact ⟨.inr (.H .rc), F.inc_HM _, (F.inc_HK _ _).2 rfl⟩
  · exact ⟨.inl (F.X .ra), F.inc_M_Xra, F.inc_pK_of (F.X_mem_AX .ra) (F.A_ne_X .ra).symm⟩
  · exact ⟨.inr (.H .r0), F.inc_HM _, (F.inc_HK _ _).2 rfl⟩

/-- Two hat lines. -/
theorem KK (s t : Row) : ∃ p : P ⊕ NewPt, F.inc p (.inr (.K s)) ∧ F.inc p (.inr (.K t)) :=
  ⟨.inr .Q, F.inc_QK s, F.inc_QK t⟩

/-- Step 3 of the proof: any two distinct lines of the new structure are concurrent. -/
theorem concurrent (l m : L ⊕ NewLn) (hlm : l ≠ m) :
    ∃ p : P ⊕ NewPt, F.inc p l ∧ F.inc p m := by
  rcases l with l | l <;> rcases m with m | m
  · exact F.pp_lines l m (fun e => hlm (congrArg Sum.inl e))
  · cases m with
    | M => exact F.pM l
    | K s => exact F.pK l s
  · cases l with
    | M => obtain ⟨p, h1, h2⟩ := F.pM m; exact ⟨p, h2, h1⟩
    | K s => obtain ⟨p, h1, h2⟩ := F.pK m s; exact ⟨p, h2, h1⟩
  · cases l with
    | M =>
      cases m with
      | M => exact absurd rfl hlm
      | K s => exact F.MK s
    | K s =>
      cases m with
      | M => obtain ⟨p, h1, h2⟩ := F.MK s; exact ⟨p, h2, h1⟩
      | K t => exact F.KK s t

end Frame

end BipartiteDD.Plus2
