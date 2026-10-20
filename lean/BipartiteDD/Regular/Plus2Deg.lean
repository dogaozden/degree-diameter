import BipartiteDD.Regular.Plus2Geom

/-! Regularity, part 2c: exact degrees in the `+2` graph.

Every point of the `+2` incidence structure has exactly `q + 2` lines through it, except the deficient points
`defPt` of the plane, which have `q + 1`. The upper bounds are those of `Plus2.Degree` (with one case
sharpened), and the lower bounds exhibit an explicit set of neighbours. For lines the upper bounds are enough:
the exact degrees follow from double counting (`line_degree_eq`). -/

namespace BipartiteDD.Plus2.Frame

open Configuration Finset
open scoped Classical
open BipartiteDD.Regular

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
variable (F : Frame P L)

theorem ncard_inl_union_inr {α β : Type*} [Finite α] [Finite β] (S : Set α) (T : Set β) :
    (Sum.inl '' S ∪ Sum.inr '' T).ncard = S.ncard + T.ncard := by
  rw [Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _),
    Set.ncard_image_of_injective _ Sum.inl_injective, Set.ncard_image_of_injective _ Sum.inr_injective]
  exact Set.disjoint_left.2 (by rintro _ ⟨a, -, rfl⟩ ⟨b, -, h⟩; cases h)

/-- The successor of a row in the 3-cycle (`ra` is fixed and never used). -/
def succ0 : Row → Row
  | .r0 => .rc
  | .r1 => .r0
  | .rc => .r1
  | .ra => .ra

theorem cyc_succ0 : ∀ t : Row, t ≠ .ra → cyc t (succ0 t) = true := by decide

theorem succ0_ne : ∀ t : Row, t ≠ .ra → succ0 t ≠ t := by decide

theorem succ0_ne_ra : ∀ t : Row, t ≠ .ra → succ0 t ≠ .ra := by decide

theorem ptNb_ncard_eq {v : P ⊕ NewPt} {S : Set (L ⊕ NewLn)} (hsub : S ⊆ F.ptNb v)
    (hS : ProjectivePlane.order P L + 2 ≤ S.ncard) :
    (F.ptNb v).ncard = ProjectivePlane.order P L + 2 :=
  le_antisymm (F.point_degree v) (hS.trans (Set.ncard_le_ncard hsub (Set.toFinite _)))

/-- `A` has degree `q + 2`. -/
theorem ptNb_A : (F.ptNb (.inl F.A)).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' {l : L | F.A ∈ l} ∪ Sum.inr '' ({NewLn.K .ra} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inl F.A) (.inl l)
      rw [F.inc_pp]
      exact Or.inl ⟨hl, fun ⟨s, hs, _⟩ => F.A_ne_X s hs⟩
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      change F.inc (.inl F.A) (.inr (.K .ra))
      rw [F.inc_pK]
      exact Or.inr ⟨rfl, rfl⟩
  · rw [ncard_inl_union_inr, ncard_lines_through, Set.ncard_singleton]

/-- A point off `ℓ`, not `A`, that is on no line `AX s` has degree `q + 1`. -/
theorem ptNb_defPt {p : P} (hp : F.defPt p) :
    (F.ptNb (.inl p)).ncard = ProjectivePlane.order P L + 1 := by
  obtain ⟨hE, hA, hX⟩ := hp
  apply le_antisymm
  · have hsub : F.ptNb (.inl p) ⊆ Sum.inl '' {l : L | p ∈ l} := by
      intro x hx
      change F.inc (.inl p) x at hx
      rcases x with l | n
      · rw [F.inc_pp] at hx
        rcases hx with ⟨h, -⟩ | ⟨t, s, -, ht, -⟩
        · exact ⟨l, h, rfl⟩
        · exact absurd (by rw [ht]; exact F.X_mem t) hE
      · rcases n with _ | s
        · exact absurd ((F.inc_pM p).1 hx).1 hE
        · rw [F.inc_pK] at hx
          rcases hx with ⟨h, -⟩ | ⟨-, h⟩
          · exact absurd h (hX s)
          · exact absurd h hA
    calc (F.ptNb (.inl p)).ncard ≤ (Sum.inl '' {l : L | p ∈ l}).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = ProjectivePlane.order P L + 1 := by
          rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_lines_through]
  · have hsub : Sum.inl '' {l : L | p ∈ l} ⊆ F.ptNb (.inl p) := by
      rintro x ⟨l, hl, rfl⟩
      change F.inc (.inl p) (.inl l)
      rw [F.inc_pp]
      exact Or.inl ⟨hl, fun ⟨s, hs, _⟩ => hE (hs ▸ F.X_mem s)⟩
    calc ProjectivePlane.order P L + 1 = (Sum.inl '' {l : L | p ∈ l}).ncard := by
          rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_lines_through]
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- A point off `ℓ`, not `A`, on a line `AX s0`, has degree `q + 2`. -/
theorem ptNb_gen {p : P} (hE : p ∉ F.ell) (hA : p ≠ F.A) {s0 : Row} (hs0 : p ∈ F.AX s0) :
    (F.ptNb (.inl p)).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' {l : L | p ∈ l} ∪ Sum.inr '' ({NewLn.K s0} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inl p) (.inl l)
      rw [F.inc_pp]
      exact Or.inl ⟨hl, fun ⟨s, hs, _⟩ => hE (hs ▸ F.X_mem s)⟩
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      change F.inc (.inl p) (.inr (.K s0))
      rw [F.inc_pK]
      exact Or.inl ⟨hs0, hA⟩
  · rw [ncard_inl_union_inr, ncard_lines_through, Set.ncard_singleton]

/-- A point of `ℓ` other than every `X t` has degree `q + 2`. -/
theorem ptNb_ell {u : P} (hu : u ∈ F.ell) (hX : ∀ t, u ≠ F.X t) :
    (F.ptNb (.inl u)).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' {l : L | u ∈ l} ∪ Sum.inr '' ({NewLn.M} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inl u) (.inl l)
      rw [F.inc_pp]
      exact Or.inl ⟨hl, fun ⟨s, hs, _⟩ => hX s hs⟩
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      change F.inc (.inl u) (.inr .M)
      rw [F.inc_pM]
      exact ⟨hu, hX _, hX _, hX _⟩
  · rw [ncard_inl_union_inr, ncard_lines_through, Set.ncard_singleton]

/-- `Xa` has degree `q + 2`. -/
theorem ptNb_Xa : (F.ptNb (.inl (F.X .ra))).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' ({l : L | F.X .ra ∈ l} \ {F.AX .ra}) ∪
    Sum.inr '' ({NewLn.M, NewLn.K .ra} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inl (F.X .ra)) (.inl l)
      rw [F.inc_pp]
      refine Or.inl ⟨hl.1, fun ⟨s, hs, hl'⟩ => hl.2 ?_⟩
      have hs' : s = .ra := (F.X_inj hs).symm
      subst hs'
      exact hl'
    · rcases hn with rfl | rfl
      · change F.inc (.inl (F.X .ra)) (.inr .M)
        rw [F.inc_pM]
        exact ⟨F.X_mem _, fun h => absurd (F.X_inj h) (by decide), fun h => absurd (F.X_inj h) (by decide),
          fun h => absurd (F.X_inj h) (by decide)⟩
      · change F.inc (.inl (F.X .ra)) (.inr (.K .ra))
        rw [F.inc_pK]
        exact Or.inl ⟨F.X_mem_AX _, (F.A_ne_X _).symm⟩
  · have h2 : ({NewLn.M, NewLn.K .ra} : Set NewLn).ncard = 2 := Set.ncard_pair (by decide)
    have h1 : ({l : L | F.X .ra ∈ l} \ {F.AX .ra}).ncard + 1 = ProjectivePlane.order P L + 1 := by
      rw [ncard_diff_one (show F.AX .ra ∈ {l : L | F.X .ra ∈ l} from F.X_mem_AX .ra), ncard_lines_through]
    rw [ncard_inl_union_inr, h2]
    omega

/-- `X t` for `t ∈ {0, 1, c}` has degree `q + 2`. -/
theorem ptNb_Xt (t : Row) (ht : t ≠ .ra) :
    (F.ptNb (.inl (F.X t))).ncard = ProjectivePlane.order P L + 2 := by
  have hnot : F.AX (succ0 t) ∉ ({l : L | F.X t ∈ l} \ {F.AX t}) := by
    rintro ⟨h, -⟩
    have := (F.mem_AX_iff (succ0 t) (F.X_mem t)).1 h
    exact succ0_ne t ht (F.X_inj this).symm
  refine F.ptNb_ncard_eq (S := Sum.inl '' (insert (F.AX (succ0 t)) ({l : L | F.X t ∈ l} \ {F.AX t})) ∪
    Sum.inr '' ({NewLn.K t} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inl (F.X t)) (.inl l)
      rw [F.inc_pp]
      rcases hl with rfl | ⟨h, hne⟩
      · exact Or.inr ⟨t, succ0 t, cyc_succ0 t ht, rfl, rfl⟩
      · refine Or.inl ⟨h, fun ⟨s, hs, hl'⟩ => hne ?_⟩
        have hs' : s = t := (F.X_inj hs).symm
        subst hs'
        exact hl'
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      change F.inc (.inl (F.X t)) (.inr (.K t))
      rw [F.inc_pK]
      exact Or.inl ⟨F.X_mem_AX _, (F.A_ne_X _).symm⟩
  · have h1 : ({l : L | F.X t ∈ l} \ {F.AX t}).ncard + 1 = ProjectivePlane.order P L + 1 := by
      rw [ncard_diff_one (show F.AX t ∈ {l : L | F.X t ∈ l} from F.X_mem_AX t), ncard_lines_through]
    rw [ncard_inl_union_inr, Set.ncard_insert_of_notMem hnot (Set.toFinite _), Set.ncard_singleton]
    omega

/-- `Q` has degree `q + 2`. -/
theorem ptNb_Q : (F.ptNb (.inr .Q)).ncard = ProjectivePlane.order P L + 2 := by
  have hZ : ({F.AX .r0, F.AX .r1, F.AX .rc} : Set L).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [F.AX_inj.ne (by decide : Row.r0 ≠ Row.r1),
      F.AX_inj.ne (by decide : Row.r0 ≠ Row.rc)]), Set.ncard_pair (F.AX_inj.ne (by decide))]
  have hZsub : ({F.AX .r0, F.AX .r1, F.AX .rc} : Set L) ⊆ {l : L | F.A ∈ l} := by
    rintro l (rfl | rfl | rfl) <;> exact F.A_mem_AX _
  have hset : {l : L | F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc} =
      {l : L | F.A ∈ l} \ {F.AX .r0, F.AX .r1, F.AX .rc} := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
    tauto
  have hdiff := Set.ncard_diff hZsub (Set.toFinite _)
  rw [hZ, ncard_lines_through] at hdiff
  have hle := Set.ncard_le_ncard hZsub (Set.toFinite _)
  rw [hZ, ncard_lines_through] at hle
  have hT : (NewLn.K '' (Set.univ : Set Row)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (fun a b h => NewLn.K.inj h), Set.ncard_univ, card_row]
  refine F.ptNb_ncard_eq (S := Sum.inl '' {l : L | F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc} ∪
    Sum.inr '' (NewLn.K '' (Set.univ : Set Row))) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, ⟨s, -, rfl⟩, rfl⟩)
    · exact (F.inc_Ql l).2 hl
    · exact F.inc_QK s
  · rw [ncard_inl_union_inr, hset, hdiff, hT]
    omega

/-- `H ra` has degree `q + 2`. -/
theorem ptNb_Hra : (F.ptNb (.inr (.H .ra))).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' {l : L | F.X .ra ∈ l} ∪ Sum.inr '' ({NewLn.M} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inr (.H .ra)) (.inl l)
      rw [F.inc_Hl]
      by_cases hle : l = F.ell
      · exact Or.inr ⟨rfl, hle⟩
      · exact Or.inl ⟨hl, hle⟩
    · rw [Set.mem_singleton_iff] at hn
      subst hn
      exact F.inc_HM .ra
  · rw [ncard_inl_union_inr, ncard_lines_through, Set.ncard_singleton]

/-- `H s` for `s ∈ {0, 1, c}` has degree `q + 2`. -/
theorem ptNb_H (s : Row) (hs : s ≠ .ra) :
    (F.ptNb (.inr (.H s))).ncard = ProjectivePlane.order P L + 2 := by
  refine F.ptNb_ncard_eq (S := Sum.inl '' ({l : L | F.X s ∈ l} \ {F.ell}) ∪
    Sum.inr '' ({NewLn.M, NewLn.K (succ0 s)} : Set NewLn)) ?_ ?_
  · rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
    · change F.inc (.inr (.H s)) (.inl l)
      rw [F.inc_Hl]
      exact Or.inl ⟨hl.1, hl.2⟩
    · rcases hn with rfl | rfl
      · exact F.inc_HM s
      · exact (F.inc_HK _ _).2 (cyc_succ0 s hs)
  · have h1 : ({l : L | F.X s ∈ l} \ {F.ell}).ncard + 1 = ProjectivePlane.order P L + 1 := by
      rw [ncard_diff_one (show F.ell ∈ {l : L | F.X s ∈ l} from F.X_mem s), ncard_lines_through]
    have h2 : ({NewLn.M, NewLn.K (succ0 s)} : Set NewLn).ncard = 2 := Set.ncard_pair (by simp)
    rw [ncard_inl_union_inr, h2]
    omega

/-- The deficient vertices of the point side: the deficient points of the plane. -/
def defV1 : P ⊕ NewPt → Prop
  | .inl p => F.defPt p
  | .inr _ => False

/-- The deficient vertices of the line side: the deficient lines of the plane. -/
def defV2 : L ⊕ NewLn → Prop
  | .inl l => F.defLn l
  | .inr _ => False

/-- Every point has degree `q + 2`, except the deficient points, which have degree `q + 1`. -/
theorem ptNb_ncard_add (v : P ⊕ NewPt) :
    (F.ptNb v).ncard + (if F.defV1 v then 1 else 0) = ProjectivePlane.order P L + 2 := by
  rcases v with u | n
  · by_cases hA : u = F.A
    · subst hA
      have : ¬ F.defV1 (.inl F.A) := fun h => h.2.1 rfl
      rw [if_neg this, F.ptNb_A]
    by_cases hu : u ∈ F.ell
    · have hnd : ¬ F.defV1 (.inl u) := fun h => h.1 hu
      rw [if_neg hnd, add_zero]
      by_cases hX : ∃ t, u = F.X t
      · obtain ⟨t, rfl⟩ := hX
        by_cases ht : t = .ra
        · subst ht
          exact F.ptNb_Xa
        · exact F.ptNb_Xt t ht
      · push Not at hX
        exact F.ptNb_ell hu hX
    · by_cases hex : ∃ s, u ∈ F.AX s
      · obtain ⟨s0, hs0⟩ := hex
        have hnd : ¬ F.defV1 (.inl u) := fun h => h.2.2 s0 hs0
        rw [if_neg hnd, add_zero]
        exact F.ptNb_gen hu hA hs0
      · push Not at hex
        have hd : F.defV1 (.inl u) := ⟨hu, hA, hex⟩
        rw [if_pos hd, F.ptNb_defPt hd]
  · have hnd : ¬ F.defV1 (.inr n) := fun h => h
    rw [if_neg hnd, add_zero]
    rcases n with _ | s
    · exact F.ptNb_Q
    · by_cases hs : s = .ra
      · subst hs
        exact F.ptNb_Hra
      · exact F.ptNb_H s hs

/-- A deficient line has at most `q + 1` points. -/
theorem lnNb_defLn_le {l : L} (hl : F.defLn l) :
    (F.lnNb (.inl l)).ncard ≤ ProjectivePlane.order P L + 1 := by
  obtain ⟨hE, hA, hX⟩ := hl
  have hsub : F.lnNb (.inl l) ⊆ Sum.inl '' {p : P | p ∈ l} := by
    intro v hv
    change F.inc v (.inl l) at hv
    rcases v with p | n
    · rw [F.inc_pp] at hv
      rcases hv with ⟨h, -⟩ | ⟨t, s, -, -, hl'⟩
      · exact ⟨p, h, rfl⟩
      · exact absurd (hl' ▸ F.A_mem_AX s) hA
    · rcases n with _ | s
      · exact absurd ((F.inc_Ql l).1 hv).1 hA
      · rw [F.inc_Hl] at hv
        rcases hv with ⟨h, -⟩ | ⟨-, e⟩
        · exact absurd h (hX s)
        · exact absurd e hE
  calc (F.lnNb (.inl l)).ncard ≤ (Sum.inl '' {p : P | p ∈ l}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = ProjectivePlane.order P L + 1 := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_points_on]

/-- Every line has degree at most `q + 2`, and at most `q + 1` when it is deficient. -/
theorem lnNb_ncard_add_le (x : L ⊕ NewLn) :
    (F.lnNb x).ncard + (if F.defV2 x then 1 else 0) ≤ ProjectivePlane.order P L + 2 := by
  by_cases hd : F.defV2 x
  · rcases x with l | n
    · have := F.lnNb_defLn_le hd
      rw [if_pos hd]
      omega
    · exact absurd hd (fun h => h)
  · rw [if_neg hd, add_zero]
    exact F.line_degree x

theorem sum_defV1 : ∑ v : P ⊕ NewPt, (if F.defV1 v then 1 else 0) = (univ.filter F.defPt).card := by
  rw [Fintype.sum_sum_type]
  have e1 : ∑ a : P, (if F.defV1 (.inl a) then 1 else 0) = ∑ a : P, (if F.defPt a then 1 else 0) :=
    sum_congr rfl fun a _ => by
      by_cases h : F.defPt a
      · rw [if_pos h, if_pos (show F.defV1 (.inl a) from h)]
      · rw [if_neg h, if_neg (show ¬ F.defV1 (.inl a) from h)]
  have e2 : ∑ n, (if F.defV1 (.inr n) then 1 else 0) = 0 :=
    sum_eq_zero fun n _ => if_neg (fun h => h)
  rw [e1, e2, add_zero]
  exact (card_filter _ _).symm

theorem sum_defV2 : ∑ x : L ⊕ NewLn, (if F.defV2 x then 1 else 0) = (univ.filter F.defLn).card := by
  rw [Fintype.sum_sum_type]
  have e1 : ∑ a : L, (if F.defV2 (.inl a) then 1 else 0) = ∑ a : L, (if F.defLn a then 1 else 0) :=
    sum_congr rfl fun a _ => by
      by_cases h : F.defLn a
      · rw [if_pos h, if_pos (show F.defV2 (.inl a) from h)]
      · rw [if_neg h, if_neg (show ¬ F.defV2 (.inl a) from h)]
  have e2 : ∑ n, (if F.defV2 (.inr n) then 1 else 0) = 0 :=
    sum_eq_zero fun n _ => if_neg (fun h => h)
  rw [e1, e2, add_zero]
  exact (card_filter _ _).symm

/-- Every line has degree `q + 2`, except the deficient lines, which have degree `q + 1`. -/
theorem lnNb_ncard_add (x : L ⊕ NewLn) :
    (F.lnNb x).ncard + (if F.defV2 x then 1 else 0) = ProjectivePlane.order P L + 2 := by
  have hsum : ∑ v : P ⊕ NewPt, (F.ptNb v).ncard = ∑ x : L ⊕ NewLn, (F.lnNb x).ncard :=
    sum_degL_eq_sum_degR F.inc
  have h1 : ∑ v : P ⊕ NewPt, ((F.ptNb v).ncard + (if F.defV1 v then 1 else 0)) =
      ∑ _v : P ⊕ NewPt, (ProjectivePlane.order P L + 2) :=
    sum_congr rfl fun v _ => F.ptNb_ncard_add v
  have hcardV1 : Fintype.card (P ⊕ NewPt) = Fintype.card (L ⊕ NewLn) := by
    have hP : Fintype.card P = ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1 := by
      exact ProjectivePlane.card_points P L
    have hL : Fintype.card L = ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1 := by
      exact ProjectivePlane.card_lines P L
    have h5 : Fintype.card NewPt = 5 := rfl
    have h5' : Fintype.card NewLn = 5 := rfl
    simp only [Fintype.card_sum, hP, hL, h5, h5']
  have hcards : (univ.filter F.defPt).card = (univ.filter F.defLn).card := by
    have a1 := F.card_defPt
    have a2 := F.card_defLn
    omega
  simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul] at h1
  rw [F.sum_defV1] at h1
  have h2 : ∑ x : L ⊕ NewLn, ((F.lnNb x).ncard + (if F.defV2 x then 1 else 0)) =
      ∑ _x : L ⊕ NewLn, (ProjectivePlane.order P L + 2) := by
    simp only [sum_add_distrib, sum_const, card_univ, smul_eq_mul]
    rw [F.sum_defV2, ← hsum, ← hcardV1]
    omega
  have := (Finset.sum_eq_sum_iff_of_le (fun x _ => F.lnNb_ncard_add_le x)).1 h2 x (mem_univ x)
  exact this

end BipartiteDD.Plus2.Frame
