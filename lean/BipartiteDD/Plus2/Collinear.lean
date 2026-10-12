import BipartiteDD.Plus2.Basic

/-! Group B: any two distinct points of the new structure lie on a common line
(REPORT.md section 4, Step 2). -/

namespace BipartiteDD.Plus2
open Configuration

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

namespace Frame
variable (F : Frame P L)

/-- A plane point on a plane line, avoiding every removed incidence. -/
theorem inc_pl_of {u : P} {l : L} (h : u ∈ l) (hn : ∀ s, u = F.X s → l ≠ F.AX s) :
    F.inc (.inl u) (.inl l) :=
  (F.inc_pp u l).2 (Or.inl ⟨h, fun ⟨s, hu, hl⟩ => hn s hu hl⟩)

/-- A plane point on a hat line `K s`. -/
theorem inc_pK_of {u : P} {s : Row} (h : u ∈ F.AX s) (hA : u ≠ F.A) :
    F.inc (.inl u) (.inr (.K s)) :=
  (F.inc_pK u s).2 (Or.inl ⟨h, hA⟩)

/-- The rotation: `X t` lies on `AX s` whenever `cyc t s`. -/
theorem inc_rot {t s : Row} (h : cyc t s = true) :
    F.inc (.inl (F.X t)) (.inl (F.AX s)) :=
  (F.inc_pp _ _).2 (Or.inr ⟨t, s, h, rfl, rfl⟩)

/-- `X s` and `A` lie on a common line. -/
theorem pair_XA (s : Row) : ∃ l : L ⊕ NewLn, F.inc (.inl (F.X s)) l ∧ F.inc (.inl F.A) l := by
  cases s
  · exact ⟨.inl (F.AX .rc), F.inc_rot rfl,
      F.inc_pl_of (F.A_mem_AX .rc) (fun t ht _ => F.A_ne_X t ht)⟩
  · exact ⟨.inl (F.AX .r0), F.inc_rot rfl,
      F.inc_pl_of (F.A_mem_AX .r0) (fun t ht _ => F.A_ne_X t ht)⟩
  · exact ⟨.inr (.K .ra), (F.inc_pK _ _).2 (Or.inl ⟨F.X_mem_AX .ra, (F.A_ne_X .ra).symm⟩),
      (F.inc_pK _ _).2 (Or.inr ⟨rfl, rfl⟩)⟩
  · exact ⟨.inl (F.AX .r1), F.inc_rot rfl,
      F.inc_pl_of (F.A_mem_AX .r1) (fun t ht _ => F.A_ne_X t ht)⟩

/-- Two distinct plane points. -/
theorem pp (u v : P) (huv : u ≠ v) : ∃ l : L ⊕ NewLn, F.inc (.inl u) l ∧ F.inc (.inl v) l := by
  obtain ⟨l0, hu, hv⟩ : ∃ l : L, u ∈ l ∧ v ∈ l :=
    ⟨_, (HasLines.mkLine_ax huv).1, (HasLines.mkLine_ax huv).2⟩
  by_cases hU : ∃ s, u = F.X s ∧ l0 = F.AX s
  · obtain ⟨s, rfl, hls⟩ := hU
    by_cases hvA : v = F.A
    · subst hvA
      exact F.pair_XA s
    · exact ⟨.inr (.K s), F.inc_pK_of (hls ▸ hu) (F.A_ne_X s).symm,
        F.inc_pK_of (hls ▸ hv) hvA⟩
  · by_cases hV : ∃ s, v = F.X s ∧ l0 = F.AX s
    · obtain ⟨s, rfl, hls⟩ := hV
      by_cases huA : u = F.A
      · subst huA
        obtain ⟨l, h1, h2⟩ := F.pair_XA s
        exact ⟨l, h2, h1⟩
      · exact ⟨.inr (.K s), F.inc_pK_of (hls ▸ hu) huA, F.inc_pK_of (hls ▸ hv) (F.A_ne_X s).symm⟩
    · exact ⟨.inl l0, F.inc_pl_of hu (fun s hus hls => hU ⟨s, hus, hls⟩),
        F.inc_pl_of hv (fun s hvs hls => hV ⟨s, hvs, hls⟩)⟩

/-- `Q` and a plane point. -/
theorem Q_pt (u : P) : ∃ l : L ⊕ NewLn, F.inc (.inr .Q) l ∧ F.inc (.inl u) l := by
  by_cases hA : u = F.A
  · subst hA
    have hP : u ≠ F.P0 := fun h => F.A_not_mem (h ▸ F.P0_mem)
    refine ⟨.inl (HasLines.mkLine hP), (F.inc_Ql _).2 ⟨(HasLines.mkLine_ax hP).1,
      ne_AX_of_mem F.P0_mem (HasLines.mkLine_ax hP).2 .r0 (F.X_ne_P0 .r0).symm,
      ne_AX_of_mem F.P0_mem (HasLines.mkLine_ax hP).2 .r1 (F.X_ne_P0 .r1).symm,
      ne_AX_of_mem F.P0_mem (HasLines.mkLine_ax hP).2 .rc (F.X_ne_P0 .rc).symm⟩,
      F.inc_pl_of (HasLines.mkLine_ax hP).1 (fun s hs _ => F.A_ne_X s hs)⟩
  · have huA : F.A ≠ u := fun h => hA h.symm
    obtain ⟨m, hAm, hum⟩ : ∃ m : L, F.A ∈ m ∧ u ∈ m :=
      ⟨_, (HasLines.mkLine_ax huA).1, (HasLines.mkLine_ax huA).2⟩
    by_cases h0 : m = F.AX .r0
    · exact ⟨.inr (.K .r0), F.inc_QK _, F.inc_pK_of (h0 ▸ hum) hA⟩
    by_cases h1 : m = F.AX .r1
    · exact ⟨.inr (.K .r1), F.inc_QK _, F.inc_pK_of (h1 ▸ hum) hA⟩
    by_cases h2 : m = F.AX .rc
    · exact ⟨.inr (.K .rc), F.inc_QK _, F.inc_pK_of (h2 ▸ hum) hA⟩
    by_cases hua : u = F.X .ra
    · exact ⟨.inr (.K .ra), F.inc_QK _, F.inc_pK_of (hua ▸ F.X_mem_AX .ra) hA⟩
    refine ⟨.inl m, (F.inc_Ql m).2 ⟨hAm, h0, h1, h2⟩, F.inc_pl_of hum ?_⟩
    intro s hs
    cases s
    · exact h0
    · exact h1
    · exact h2
    · exact absurd hs hua

/-- A common line of `H s` and `X s`. -/
theorem H_gen (s : Row) : ∃ l : L ⊕ NewLn, F.inc (.inr (.H s)) l ∧ F.inc (.inl (F.X s)) l := by
  obtain ⟨m, hXm, hmℓ, hmA⟩ := exists_line_ne (F.X s) F.ell (F.AX s)
  refine ⟨.inl m, (F.inc_Hl s m).2 (Or.inl ⟨hXm, hmℓ⟩), F.inc_pl_of hXm ?_⟩
  intro t ht
  have hst : s = t := F.X_inj ht
  subst hst
  exact hmA

/-- `X ra` is on `M`. -/
theorem inc_M_Xra : F.inc (.inl (F.X .ra)) (.inr .M) :=
  (F.inc_pM _).2 ⟨F.X_mem .ra, F.X_ne (by decide), F.X_ne (by decide), F.X_ne (by decide)⟩

/-- `H s` and `X t` for `t ≠ s`. -/
theorem H_X (s t : Row) (hst : s ≠ t) :
    ∃ l : L ⊕ NewLn, F.inc (.inr (.H s)) l ∧ F.inc (.inl (F.X t)) l := by
  rcases s with _ | _ | _ | _ <;> rcases t with _ | _ | _ | _
  -- s = r0
  · exact absurd rfl hst
  · exact ⟨.inl (F.AX .r0), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX .r0, F.AX_ne_ell .r0⟩),
      F.inc_rot rfl⟩
  · exact ⟨.inr .M, F.inc_HM _, F.inc_M_Xra⟩
  · exact ⟨.inr (.K .rc), (F.inc_HK _ _).2 rfl, F.inc_pK_of (F.X_mem_AX .rc) (F.A_ne_X .rc).symm⟩
  -- s = r1
  · exact ⟨.inr (.K .r0), (F.inc_HK _ _).2 rfl, F.inc_pK_of (F.X_mem_AX .r0) (F.A_ne_X .r0).symm⟩
  · exact absurd rfl hst
  · exact ⟨.inr .M, F.inc_HM _, F.inc_M_Xra⟩
  · exact ⟨.inl (F.AX .r1), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX .r1, F.AX_ne_ell .r1⟩),
      F.inc_rot rfl⟩
  -- s = ra: the line ℓ
  · exact ⟨.inl F.ell, (F.inc_Hl _ _).2 (Or.inr ⟨rfl, rfl⟩),
      F.inc_pl_of (F.X_mem .r0) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
  · exact ⟨.inl F.ell, (F.inc_Hl _ _).2 (Or.inr ⟨rfl, rfl⟩),
      F.inc_pl_of (F.X_mem .r1) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
  · exact absurd rfl hst
  · exact ⟨.inl F.ell, (F.inc_Hl _ _).2 (Or.inr ⟨rfl, rfl⟩),
      F.inc_pl_of (F.X_mem .rc) (fun u _ hl => F.AX_ne_ell u hl.symm)⟩
  -- s = rc
  · exact ⟨.inl (F.AX .rc), (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX .rc, F.AX_ne_ell .rc⟩),
      F.inc_rot rfl⟩
  · exact ⟨.inr (.K .r1), (F.inc_HK _ _).2 rfl, F.inc_pK_of (F.X_mem_AX .r1) (F.A_ne_X .r1).symm⟩
  · exact ⟨.inr .M, F.inc_HM _, F.inc_M_Xra⟩
  · exact absurd rfl hst

/-- `H s` and a plane point `u`. -/
theorem H_pt (s : Row) (u : P) : ∃ l : L ⊕ NewLn, F.inc (.inr (.H s)) l ∧ F.inc (.inl u) l := by
  by_cases hu : u ∈ F.ell
  · by_cases hX : ∃ t, u = F.X t
    · obtain ⟨t, rfl⟩ := hX
      by_cases hts : t = s
      · subst hts
        exact F.H_gen t
      · obtain ⟨l, h1, h2⟩ := F.H_X s t (fun h => hts h.symm)
        exact ⟨l, h1, h2⟩
    · push_neg at hX
      exact ⟨.inr .M, F.inc_HM s, (F.inc_pM u).2 ⟨hu, hX .r0, hX .r1, hX .rc⟩⟩
  · have hXu : F.X s ≠ u := fun h => hu (by rw [← h]; exact F.X_mem s)
    obtain ⟨m, hXm, hum⟩ : ∃ m : L, F.X s ∈ m ∧ u ∈ m :=
      ⟨_, (HasLines.mkLine_ax hXu).1, (HasLines.mkLine_ax hXu).2⟩
    refine ⟨.inl m, (F.inc_Hl s m).2 (Or.inl ⟨hXm, fun e => hu (by rw [e] at hum; exact hum)⟩),
      F.inc_pl_of hum ?_⟩
    intro t ht _
    exact hu (by rw [ht]; exact F.X_mem t)

/-- `Q` and `H s`. -/
theorem QH (s : Row) : ∃ l : L ⊕ NewLn, F.inc (.inr .Q) l ∧ F.inc (.inr (.H s)) l := by
  rcases s with _ | _ | _ | _
  · exact ⟨.inr (.K .rc), F.inc_QK _, (F.inc_HK _ _).2 rfl⟩
  · exact ⟨.inr (.K .r0), F.inc_QK _, (F.inc_HK _ _).2 rfl⟩
  · refine ⟨.inl (F.AX .ra), (F.inc_Ql _).2 ⟨F.A_mem_AX .ra, ?_, ?_, ?_⟩,
      (F.inc_Hl _ _).2 (Or.inl ⟨F.X_mem_AX .ra, F.AX_ne_ell .ra⟩)⟩
    · exact fun e => absurd (F.AX_inj e) (by decide)
    · exact fun e => absurd (F.AX_inj e) (by decide)
    · exact fun e => absurd (F.AX_inj e) (by decide)
  · exact ⟨.inr (.K .r1), F.inc_QK _, (F.inc_HK _ _).2 rfl⟩

/-- Two new hat points. -/
theorem HH (s t : Row) : ∃ l : L ⊕ NewLn, F.inc (.inr (.H s)) l ∧ F.inc (.inr (.H t)) l :=
  ⟨.inr .M, F.inc_HM s, F.inc_HM t⟩

/-- Step 2 of the proof: any two distinct points of the new structure are collinear. -/
theorem collinear (p q : P ⊕ NewPt) (hpq : p ≠ q) :
    ∃ l : L ⊕ NewLn, F.inc p l ∧ F.inc q l := by
  rcases p with u | x <;> rcases q with v | y
  · exact F.pp u v (fun e => hpq (congrArg Sum.inl e))
  · cases y with
    | Q => obtain ⟨l, h1, h2⟩ := F.Q_pt u; exact ⟨l, h2, h1⟩
    | H s => obtain ⟨l, h1, h2⟩ := F.H_pt s u; exact ⟨l, h2, h1⟩
  · cases x with
    | Q => exact F.Q_pt v
    | H s => exact F.H_pt s v
  · cases x with
    | Q =>
      cases y with
      | Q => exact absurd rfl hpq
      | H s => exact F.QH s
    | H s =>
      cases y with
      | Q => obtain ⟨l, h1, h2⟩ := F.QH s; exact ⟨l, h2, h1⟩
      | H t => exact F.HH s t

end Frame

end BipartiteDD.Plus2
