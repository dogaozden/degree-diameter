import BipartiteDD.Plus2.Concurrent

/-! Group D: every vertex of the new incidence graph has degree at most `q + 2`
(REPORT.md section 4, Step 1). Each neighbourhood is covered by an explicit set of plane
objects together with an explicit set of new objects, and the sizes are counted with `Set.ncard`. -/

namespace BipartiteDD.Plus2
open Configuration

/-! ### Counting helpers -/

section Counting

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

/-- The lines through a point of a finite projective plane: `q + 1` of them. -/
theorem ncard_lines_through [Finite P] [Finite L] (p : P) :
    ({l : L | p ∈ l}).ncard = order P L + 1 := by
  rw [← Set.Nat.card_coe_set_eq]
  exact lineCount_eq (P := P) (L := L) p

/-- The points of a line of a finite projective plane: `q + 1` of them. -/
theorem ncard_points_on [Finite P] [Finite L] (l : L) :
    ({p : P | p ∈ l}).ncard = order P L + 1 := by
  rw [← Set.Nat.card_coe_set_eq]
  exact pointCount_eq (P := P) (L := L) l

end Counting

/-- A set covered by the images of `S` and `T` has at most `|S| + |T|` elements. -/
theorem ncard_le_sum {α β : Type*} [Finite α] [Finite β] (N : Set (α ⊕ β)) (S : Set α)
    (T : Set β) (h : N ⊆ Sum.inl '' S ∪ Sum.inr '' T) : N.ncard ≤ S.ncard + T.ncard := by
  calc N.ncard ≤ (Sum.inl '' S ∪ Sum.inr '' T).ncard := Set.ncard_le_ncard h (Set.toFinite _)
    _ ≤ (Sum.inl '' S).ncard + (Sum.inr '' T).ncard := Set.ncard_union_le _ _
    _ = S.ncard + T.ncard := by
      rw [Set.ncard_image_of_injective _ Sum.inl_injective,
        Set.ncard_image_of_injective _ Sum.inr_injective]

/-- A set whose elements are all equal has at most one element. -/
theorem ncard_le_one_of {α : Type*} [Finite α] (S : Set α) (h : ∀ x ∈ S, ∀ y ∈ S, x = y) :
    S.ncard ≤ 1 :=
  (Set.ncard_le_one_iff (Set.toFinite _)).2 h

/-- Three distinct elements of `T`, none in `S ⊆ T`: `|S| + 3 ≤ |T|`. -/
theorem ncard_add_three_le {α : Type*} [Finite α] (S T : Set α) (a b c : α) (ha : a ∈ T)
    (hb : b ∈ T) (hc : c ∈ T) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hS : ∀ x ∈ S, x ≠ a ∧ x ≠ b ∧ x ≠ c) (hsub : S ⊆ T) : S.ncard + 3 ≤ T.ncard := by
  have hZ : ({a, b, c} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  have hdisj : Disjoint S ({a, b, c} : Set α) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx' with rfl | rfl | rfl
    · exact (hS x hx).1 rfl
    · exact (hS x hx).2.1 rfl
    · exact (hS x hx).2.2 rfl
  have hU : (S ∪ {a, b, c}).ncard = S.ncard + 3 := by
    rw [Set.ncard_union_eq hdisj, hZ]
  have hsub' : S ∪ {a, b, c} ⊆ T := by
    intro x hx
    rcases hx with hx | hx
    · exact hsub hx
    · rcases hx with rfl | rfl | rfl
      · exact ha
      · exact hb
      · exact hc
  have := Set.ncard_le_ncard hsub' (Set.toFinite _)
  omega

/-- Removing a member of a set lowers its size by one. -/
theorem ncard_diff_one {α : Type*} [Finite α] {S : Set α} {a : α} (ha : a ∈ S) :
    (S \ {a}).ncard + 1 = S.ncard := by
  rw [← Set.ncard_diff_singleton_add_one ha (Set.toFinite _)]

/-! ### Facts about the 3-cycle -/

theorem cyc_ra_left : ∀ s : Row, cyc .ra s = false := by decide

theorem cyc_ra_right : ∀ s : Row, cyc s .ra = false := by decide

/-- Outgoing from a row there is at most one `cyc` partner. -/
theorem cyc_out_unique : ∀ s x y : Row, cyc s x = true → cyc s y = true → x = y := by decide

/-- Incoming to a row there is at most one `cyc` partner. -/
theorem cyc_in_unique : ∀ t s s' : Row, cyc s t = true → cyc s' t = true → s = s' := by decide

namespace Frame

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]
variable (F : Frame P L)

/-- The lines incident to a point of the new structure. -/
def ptNb (v : P ⊕ NewPt) : Set (L ⊕ NewLn) := {x | F.inc v x}

/-- The points incident to a line of the new structure. -/
def lnNb (x : L ⊕ NewLn) : Set (P ⊕ NewPt) := {v | F.inc v x}

theorem neighborSet_inl (v : P ⊕ NewPt) :
    F.graph.neighborSet (.inl v) = Sum.inr '' F.ptNb v := by
  ext w
  rcases w with x | x
  · constructor
    · intro h
      exact absurd h (fun h' => h')
    · rintro ⟨y, _, hy⟩
      cases hy
  · constructor
    · intro h
      exact ⟨x, h, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact hy

theorem neighborSet_inr (x : L ⊕ NewLn) :
    F.graph.neighborSet (.inr x) = Sum.inl '' F.lnNb x := by
  ext w
  rcases w with v | y
  · constructor
    · intro h
      exact ⟨v, h, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact hz
  · constructor
    · intro h
      exact absurd h (fun h' => h')
    · rintro ⟨z, _, hz⟩
      cases hz

/-! ### Degrees of points -/

theorem pt_A [Finite P] [Finite L] : (F.ptNb (.inl F.A)).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inl F.A) ⊆
      Sum.inl '' {l : L | F.A ∈ l} ∪ Sum.inr '' {NewLn.K .ra} := by
    intro x hx
    change F.inc (.inl F.A) x at hx
    rcases x with l | n
    · rw [F.inc_pp] at hx
      rcases hx with ⟨h, -⟩ | ⟨t, s, -, ht, -⟩
      · exact Or.inl ⟨l, h, rfl⟩
      · exact absurd ht (F.A_ne_X t)
    · rcases n with _ | s
      · exact absurd ((F.inc_pM F.A).1 hx).1 F.A_not_mem
      · rw [F.inc_pK] at hx
        rcases hx with ⟨-, h⟩ | ⟨rfl, -⟩
        · exact absurd rfl h
        · exact Or.inr ⟨_, rfl, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  rw [ncard_lines_through, Set.ncard_singleton] at h1
  omega

/-- A plane point off `ℓ`, not `A`: its lines through it, and at most one hat line. -/
theorem pt_gen [Finite P] [Finite L] (u : P) (hu : u ∉ F.ell) (hA : u ≠ F.A) :
    (F.ptNb (.inl u)).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inl u) ⊆
      Sum.inl '' {l : L | u ∈ l} ∪ Sum.inr '' (NewLn.K '' {s : Row | u ∈ F.AX s}) := by
    intro x hx
    change F.inc (.inl u) x at hx
    rcases x with l | n
    · rw [F.inc_pp] at hx
      rcases hx with ⟨h, -⟩ | ⟨t, s, -, ht, -⟩
      · exact Or.inl ⟨l, h, rfl⟩
      · exact absurd (by rw [ht]; exact F.X_mem t) hu
    · rcases n with _ | s
      · exact absurd ((F.inc_pM u).1 hx).1 hu
      · rw [F.inc_pK] at hx
        rcases hx with ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inr ⟨NewLn.K s, ⟨s, h, rfl⟩, rfl⟩
        · exact absurd h hA
  have hR : ({s : Row | u ∈ F.AX s}).ncard ≤ 1 := by
    apply ncard_le_one_of
    intro s hs t ht
    by_contra hst
    exact hA (F.eq_A_of_mem_AX_AX hst hs ht)
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : (NewLn.K '' {s : Row | u ∈ F.AX s}).ncard ≤ ({s : Row | u ∈ F.AX s}).ncard :=
    Set.ncard_image_le (Set.toFinite _)
  rw [ncard_lines_through] at h1
  omega

/-- A plane point on `ℓ` other than all `X s`: its lines, and `M`. -/
theorem pt_ell [Finite P] [Finite L] (u : P) (hu : u ∈ F.ell) (hX : ∀ t, u ≠ F.X t) :
    (F.ptNb (.inl u)).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inl u) ⊆
      Sum.inl '' {l : L | u ∈ l} ∪ Sum.inr '' {NewLn.M} := by
    intro x hx
    change F.inc (.inl u) x at hx
    rcases x with l | n
    · rw [F.inc_pp] at hx
      rcases hx with ⟨h, -⟩ | ⟨t, s, -, ht, -⟩
      · exact Or.inl ⟨l, h, rfl⟩
      · exact absurd ht (hX t)
    · rcases n with _ | s
      · exact Or.inr ⟨_, rfl, rfl⟩
      · rw [F.inc_pK] at hx
        rcases hx with ⟨h, -⟩ | ⟨-, h⟩
        · exact absurd ((F.mem_AX_iff s hu).1 h) (hX s)
        · exact F.A_not_mem (by rw [← h]; exact hu)
  have h1 := ncard_le_sum _ _ _ hsub
  rw [ncard_lines_through, Set.ncard_singleton] at h1
  omega

/-- The plane point `X ra = Xa`: `AXa` loses it, and it meets `M` and `Ka`. -/
theorem pt_Xa [Finite P] [Finite L] : (F.ptNb (.inl (F.X .ra))).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inl (F.X .ra)) ⊆
      Sum.inl '' ({l : L | F.X .ra ∈ l} \ {F.AX .ra}) ∪
        Sum.inr '' ({NewLn.M, NewLn.K .ra} : Set NewLn) := by
    intro x hx
    change F.inc (.inl (F.X .ra)) x at hx
    rcases x with l | n
    · rw [F.inc_pp] at hx
      rcases hx with ⟨h, hn⟩ | ⟨t, s, hc, ht, -⟩
      · exact Or.inl ⟨l, ⟨h, fun e => hn ⟨.ra, rfl, e⟩⟩, rfl⟩
      · have htr : t = .ra := (F.X_inj ht).symm
        subst htr
        rw [cyc_ra_left] at hc
        exact absurd hc (by decide)
    · rcases n with _ | s
      · exact Or.inr ⟨_, Set.mem_insert _ _, rfl⟩
      · rw [F.inc_pK] at hx
        rcases hx with ⟨h, -⟩ | ⟨rfl, h⟩
        · have hs : s = .ra := (F.X_inj ((F.mem_AX_iff s (F.X_mem .ra)).1 h)).symm
          subst hs
          exact Or.inr ⟨_, Set.mem_insert_of_mem _ rfl, rfl⟩
        · exact absurd h.symm (F.A_ne_X .ra)
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({l : L | F.X .ra ∈ l} \ {F.AX .ra}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (F.X_mem_AX .ra), ncard_lines_through]
  have h3 : ({NewLn.M, NewLn.K .ra} : Set NewLn).ncard = 2 :=
    Set.ncard_pair (by decide)
  omega

/-- A plane point `X t` with `t ∈ {0, 1, c}`: `AX t` loses it, the rotation gives one more
line, and it meets `K t`. -/
theorem pt_Xt [Finite P] [Finite L] (t : Row) (ht : t ≠ .ra) :
    (F.ptNb (.inl (F.X t))).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inl (F.X t)) ⊆
      Sum.inl '' (({l : L | F.X t ∈ l} \ {F.AX t}) ∪
        F.AX '' {s : Row | cyc t s = true}) ∪
        Sum.inr '' ({NewLn.K t} : Set NewLn) := by
    intro x hx
    change F.inc (.inl (F.X t)) x at hx
    rcases x with l | n
    · rw [F.inc_pp] at hx
      rcases hx with ⟨h, hn⟩ | ⟨t', s, hc, ht', hl⟩
      · exact Or.inl ⟨l, Or.inl ⟨h, fun e => hn ⟨t, rfl, e⟩⟩, rfl⟩
      · have htt : t' = t := (F.X_inj ht').symm
        subst htt
        exact Or.inl ⟨l, Or.inr ⟨s, hc, hl.symm⟩, rfl⟩
    · rcases n with _ | s
      · exfalso
        obtain ⟨-, h2, h3, h4⟩ := (F.inc_pM _).1 hx
        rcases t with _ | _ | _ | _ <;>
          first | exact h2 rfl | exact h3 rfl | exact h4 rfl | exact ht rfl
      · rw [F.inc_pK] at hx
        rcases hx with ⟨h, -⟩ | ⟨-, h⟩
        · have hs : s = t := (F.X_inj ((F.mem_AX_iff s (F.X_mem t)).1 h)).symm
          subst hs
          exact Or.inr ⟨_, rfl, rfl⟩
        · exact absurd h.symm (F.A_ne_X t)
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({l : L | F.X t ∈ l} \ {F.AX t}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (F.X_mem_AX t), ncard_lines_through]
  have h3 : (F.AX '' {s : Row | cyc t s = true}).ncard ≤ 1 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans (ncard_le_one_of _ ?_)
    intro x hx y hy
    exact cyc_out_unique t x y hx hy
  have h4 : (({l : L | F.X t ∈ l} \ {F.AX t}) ∪ F.AX '' {s : Row | cyc t s = true}).ncard ≤
      order P L + 1 := by
    refine (Set.ncard_union_le _ _).trans ?_
    omega
  have h5 : ({NewLn.K t} : Set NewLn).ncard = 1 := Set.ncard_singleton _
  have h6 := ncard_le_sum _ _ _ hsub
  have h7 := Set.ncard_image_le (f := Sum.inl) (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ Sum.inl_injective] at h1
  rw [Set.ncard_image_of_injective _ Sum.inr_injective] at h1
  omega

/-- `Q`: its lines through `A` other than `AX 0, AX 1, AX c`, and all four hat lines. -/
theorem pt_Q [Finite P] [Finite L] : (F.ptNb (.inr .Q)).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inr .Q) ⊆
      Sum.inl '' {l : L | F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc} ∪
        Sum.inr '' (NewLn.K '' (Set.univ : Set Row)) := by
    intro x hx
    change F.inc (.inr .Q) x at hx
    rcases x with l | n
    · exact Or.inl ⟨l, (F.inc_Ql l).1 hx, rfl⟩
    · rcases n with _ | s
      · exact absurd hx F.not_inc_QM
      · exact Or.inr ⟨_, ⟨_, Set.mem_univ _, rfl⟩, rfl⟩
  have hT : (NewLn.K '' (Set.univ : Set Row)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (fun a b h => NewLn.K.inj h), Set.ncard_univ]
    rfl
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_add_three_le
    {l : L | F.A ∈ l ∧ l ≠ F.AX .r0 ∧ l ≠ F.AX .r1 ∧ l ≠ F.AX .rc} {l : L | F.A ∈ l}
    (F.AX .r0) (F.AX .r1) (F.AX .rc) (F.A_mem_AX _) (F.A_mem_AX _) (F.A_mem_AX _)
    (fun e => absurd (F.AX_inj e) (by decide))
    (fun e => absurd (F.AX_inj e) (by decide))
    (fun e => absurd (F.AX_inj e) (by decide))
    (fun x hx => ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩) (fun x hx => hx.1)
  rw [ncard_lines_through] at h2
  omega

/-- `Hra`: all lines through `Xa`, and `M`. -/
theorem pt_Hra [Finite P] [Finite L] : (F.ptNb (.inr (.H .ra))).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inr (.H .ra)) ⊆
      Sum.inl '' {l : L | F.X .ra ∈ l} ∪ Sum.inr '' ({NewLn.M} : Set NewLn) := by
    intro x hx
    change F.inc (.inr (.H .ra)) x at hx
    rcases x with l | n
    · rcases (F.inc_Hl .ra l).1 hx with ⟨h, -⟩ | ⟨-, e⟩
      · exact Or.inl ⟨l, h, rfl⟩
      · exact Or.inl ⟨l, by rw [e]; exact F.X_mem .ra, rfl⟩
    · rcases n with _ | s
      · exact Or.inr ⟨_, rfl, rfl⟩
      · exact absurd ((F.inc_HK _ _).1 hx) (by rw [cyc_ra_left]; decide)
  have h1 := ncard_le_sum _ _ _ hsub
  rw [ncard_lines_through, Set.ncard_singleton] at h1
  omega

/-- `H s` for `s ∈ {0, 1, c}`: the lines through `X s` other than `ℓ`, `M`, and one hat line. -/
theorem pt_H [Finite P] [Finite L] (s : Row) (hs : s ≠ .ra) :
    (F.ptNb (.inr (.H s))).ncard ≤ order P L + 2 := by
  have hsub : F.ptNb (.inr (.H s)) ⊆
      Sum.inl '' ({l : L | F.X s ∈ l} \ {F.ell}) ∪
        Sum.inr '' (({NewLn.M} : Set NewLn) ∪ NewLn.K '' {t : Row | cyc s t = true}) := by
    intro x hx
    change F.inc (.inr (.H s)) x at hx
    rcases x with l | n
    · rcases (F.inc_Hl s l).1 hx with ⟨h, h'⟩ | ⟨e, -⟩
      · exact Or.inl ⟨l, ⟨h, h'⟩, rfl⟩
      · exact absurd e hs
    · rcases n with _ | t
      · exact Or.inr ⟨_, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨_, Or.inr ⟨t, (F.inc_HK s t).1 hx, rfl⟩, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({l : L | F.X s ∈ l} \ {F.ell}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (show F.ell ∈ {l : L | F.X s ∈ l} from F.X_mem s), ncard_lines_through]
  have h3 : (({NewLn.M} : Set NewLn) ∪ NewLn.K '' {t : Row | cyc s t = true}).ncard ≤ 2 := by
    refine (Set.ncard_union_le _ _).trans ?_
    have h4 : (NewLn.K '' {t : Row | cyc s t = true}).ncard ≤ 1 := by
      refine (Set.ncard_image_le (Set.toFinite _)).trans (ncard_le_one_of _ ?_)
      intro x hx y hy
      exact cyc_out_unique s x y hx hy
    rw [Set.ncard_singleton]
    omega
  omega

/-! ### Degrees of lines -/

/-- The line `ℓ`: its `q + 1` points, and `H ra`. -/
theorem ln_ell [Finite P] [Finite L] : (F.lnNb (.inl F.ell)).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inl F.ell) ⊆
      Sum.inl '' {p : P | p ∈ F.ell} ∪ Sum.inr '' ({NewPt.H .ra} : Set NewPt) := by
    intro v hv
    change F.inc v (.inl F.ell) at hv
    rcases v with p | n
    · rw [F.inc_pp] at hv
      rcases hv with ⟨h, -⟩ | ⟨t, s, -, -, hl⟩
      · exact Or.inl ⟨p, h, rfl⟩
      · exact absurd hl.symm (F.AX_ne_ell s)
    · rcases n with _ | s
      · exact absurd hv.1 F.A_not_mem
      · rw [F.inc_Hl] at hv
        rcases hv with ⟨h, -⟩ | ⟨rfl, -⟩
        · exact absurd rfl h
        · exact Or.inr ⟨_, rfl, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  rw [ncard_points_on, Set.ncard_singleton] at h1
  omega

/-- The line `AXa`: its points other than `Xa`, and `Q`, `Ha`. -/
theorem ln_AXa [Finite P] [Finite L] :
    (F.lnNb (.inl (F.AX .ra))).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inl (F.AX .ra)) ⊆
      Sum.inl '' ({p : P | p ∈ F.AX .ra} \ {F.X .ra}) ∪
        Sum.inr '' ({NewPt.Q, NewPt.H .ra} : Set NewPt) := by
    intro v hv
    change F.inc v (.inl (F.AX .ra)) at hv
    rcases v with p | n
    · rw [F.inc_pp] at hv
      rcases hv with ⟨h, hn⟩ | ⟨t, s, hc, -, hl⟩
      · exact Or.inl ⟨p, ⟨h, fun e => hn ⟨.ra, e, rfl⟩⟩, rfl⟩
      · have hs : s = .ra := (F.AX_inj hl).symm
        subst hs
        rw [cyc_ra_right] at hc
        exact absurd hc (by decide)
    · rcases n with _ | s
      · exact Or.inr ⟨_, Set.mem_insert _ _, rfl⟩
      · rw [F.inc_Hl] at hv
        rcases hv with ⟨h, -⟩ | ⟨-, e⟩
        · have hs : s = .ra := (F.X_inj ((F.mem_AX_iff .ra (F.X_mem s)).1 h)).symm
          subst hs
          exact Or.inr ⟨_, Set.mem_insert_of_mem _ rfl, rfl⟩
        · exact absurd e (F.AX_ne_ell .ra)
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({p : P | p ∈ F.AX .ra} \ {F.X .ra}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (F.X_mem_AX .ra), ncard_points_on]
  have h3 : ({NewPt.Q, NewPt.H .ra} : Set NewPt).ncard = 2 := Set.ncard_pair (by decide)
  omega

/-- The line `AX t` for `t ∈ {0, 1, c}`: its points other than `X t`, the rotated `X s`,
and `Ht`. -/
theorem ln_AXt [Finite P] [Finite L] (t : Row) (ht : t ≠ .ra) :
    (F.lnNb (.inl (F.AX t))).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inl (F.AX t)) ⊆
      Sum.inl '' (({p : P | p ∈ F.AX t} \ {F.X t}) ∪ F.X '' {s : Row | cyc s t = true}) ∪
        Sum.inr '' ({NewPt.H t} : Set NewPt) := by
    intro v hv
    change F.inc v (.inl (F.AX t)) at hv
    rcases v with p | n
    · rw [F.inc_pp] at hv
      rcases hv with ⟨h, hn⟩ | ⟨s', s, hc, hp, hl⟩
      · exact Or.inl ⟨p, Or.inl ⟨h, fun e => hn ⟨t, e, rfl⟩⟩, rfl⟩
      · have hst : t = s := F.AX_inj hl.symm
        subst hst
        exact Or.inl ⟨p, Or.inr ⟨s', hc, hp.symm⟩, rfl⟩
    · rcases n with _ | s
      · exfalso
        obtain ⟨-, h2, h3, h4⟩ := (F.inc_Ql _).1 hv
        rcases t with _ | _ | _ | _ <;>
          first | exact h2 rfl | exact h3 rfl | exact h4 rfl | exact ht rfl
      · rw [F.inc_Hl] at hv
        rcases hv with ⟨h, -⟩ | ⟨-, e⟩
        · have hs : s = t := (F.X_inj ((F.mem_AX_iff t (F.X_mem s)).1 h)).symm
          subst hs
          exact Or.inr ⟨_, rfl, rfl⟩
        · exact absurd e (F.AX_ne_ell t)
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({p : P | p ∈ F.AX t} \ {F.X t}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (F.X_mem_AX t), ncard_points_on]
  have h3 : (F.X '' {s : Row | cyc s t = true}).ncard ≤ 1 := by
    refine (Set.ncard_image_le (Set.toFinite _)).trans (ncard_le_one_of _ ?_)
    intro x hx y hy
    exact cyc_in_unique t x y hx hy
  have h4 : (({p : P | p ∈ F.AX t} \ {F.X t}) ∪ F.X '' {s : Row | cyc s t = true}).ncard ≤
      order P L + 1 := by
    refine (Set.ncard_union_le _ _).trans ?_
    omega
  have h5 : ({NewPt.H t} : Set NewPt).ncard = 1 := Set.ncard_singleton _
  omega

/-- A line `l` that is neither `ℓ` nor any `AX s`: its `q + 1` points, and at most one new
point (`Q` needs `A ∈ l`, `H s` needs `X s ∈ l`, and two of these force `l = AX s` or `ℓ`). -/
theorem ln_gen [Finite P] [Finite L] (l : L) (hℓ : l ≠ F.ell) (hAX : ∀ s, l ≠ F.AX s) :
    (F.lnNb (.inl l)).ncard ≤ order P L + 2 := by
  have hT : ∀ x ∈ {x : NewPt | F.inc (.inr x) (.inl l)}, ∀ y ∈ {x : NewPt | F.inc (.inr x) (.inl l)},
      x = y := by
    intro x hx y hy
    change F.inc (.inr x) (.inl l) at hx
    change F.inc (.inr y) (.inl l) at hy
    rcases x with _ | s <;> rcases y with _ | t
    · rfl
    · rw [F.inc_Ql] at hx
      rw [F.inc_Hl] at hy
      rcases hy with ⟨hy, -⟩ | ⟨-, e⟩
      · exact absurd (F.eq_AX_of_mem t hx.1 hy) (hAX t)
      · exact absurd e hℓ
    · rw [F.inc_Hl] at hx
      rw [F.inc_Ql] at hy
      rcases hx with ⟨hx, -⟩ | ⟨-, e⟩
      · exact absurd (F.eq_AX_of_mem s hy.1 hx) (hAX s)
      · exact absurd e hℓ
    · rw [F.inc_Hl] at hx hy
      rcases hx with ⟨hx, -⟩ | ⟨-, e⟩
      · rcases hy with ⟨hy, -⟩ | ⟨-, e'⟩
        · by_contra hst
          rcases Nondegenerate.eq_or_eq (F.X_mem s) (F.X_mem t) hx hy with e | e
          · exact hst (congrArg NewPt.H (F.X_inj e))
          · exact hℓ e.symm
        · exact absurd e' hℓ
      · exact absurd e hℓ
  have hsub : F.lnNb (.inl l) ⊆
      Sum.inl '' {p : P | p ∈ l} ∪ Sum.inr '' {x : NewPt | F.inc (.inr x) (.inl l)} := by
    intro v hv
    change F.inc v (.inl l) at hv
    rcases v with p | x
    · rw [F.inc_pp] at hv
      rcases hv with ⟨h, -⟩ | ⟨t, s, -, -, hl⟩
      · exact Or.inl ⟨p, h, rfl⟩
      · exact absurd hl (hAX s)
    · exact Or.inr ⟨x, hv, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({x : NewPt | F.inc (.inr x) (.inl l)}).ncard ≤ 1 := ncard_le_one_of _ hT
  rw [ncard_points_on] at h1
  omega

/-- The line `M`: the points of `ℓ` other than `X 0, X 1, X c`, and the four hat points
`H s`. -/
theorem ln_M [Finite P] [Finite L] : (F.lnNb (.inr .M)).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inr .M) ⊆
      Sum.inl '' {p : P | p ∈ F.ell ∧ p ≠ F.X .r0 ∧ p ≠ F.X .r1 ∧ p ≠ F.X .rc} ∪
        Sum.inr '' (NewPt.H '' (Set.univ : Set Row)) := by
    intro v hv
    change F.inc v (.inr .M) at hv
    rcases v with p | n
    · rw [F.inc_pM] at hv
      exact Or.inl ⟨p, hv, rfl⟩
    · rcases n with _ | s
      · exact absurd hv F.not_inc_QM
      · exact Or.inr ⟨_, ⟨s, Set.mem_univ _, rfl⟩, rfl⟩
  have hT : (NewPt.H '' (Set.univ : Set Row)).ncard = 4 := by
    rw [Set.ncard_image_of_injective _ (fun a b h => NewPt.H.inj h), Set.ncard_univ]
    rfl
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_add_three_le
    {p : P | p ∈ F.ell ∧ p ≠ F.X .r0 ∧ p ≠ F.X .r1 ∧ p ≠ F.X .rc} {p : P | p ∈ F.ell}
    (F.X .r0) (F.X .r1) (F.X .rc) (F.X_mem _) (F.X_mem _) (F.X_mem _)
    (fun e => absurd (F.X_inj e) (by decide))
    (fun e => absurd (F.X_inj e) (by decide))
    (fun e => absurd (F.X_inj e) (by decide))
    (fun x hx => ⟨hx.2.1, hx.2.2.1, hx.2.2.2⟩) (fun x hx => hx.1)
  rw [ncard_points_on] at h2
  omega

/-- The line `Ka`: the points of `AXa` (including `A`), and `Q`. -/
theorem ln_Kra [Finite P] [Finite L] : (F.lnNb (.inr (.K .ra))).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inr (.K .ra)) ⊆
      Sum.inl '' {p : P | p ∈ F.AX .ra} ∪ Sum.inr '' ({NewPt.Q} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr (.K .ra)) at hv
    rcases v with p | n
    · rw [F.inc_pK] at hv
      rcases hv with ⟨h, -⟩ | ⟨-, h⟩
      · exact Or.inl ⟨p, h, rfl⟩
      · exact Or.inl ⟨p, by rw [h]; exact F.A_mem_AX .ra, rfl⟩
    · rcases n with _ | s
      · exact Or.inr ⟨_, rfl, rfl⟩
      · have h := (F.inc_HK s .ra).1 hv
        rw [cyc_ra_right] at h
        exact absurd h (by decide)
  have h1 := ncard_le_sum _ _ _ hsub
  rw [ncard_points_on, Set.ncard_singleton] at h1
  omega

/-- The line `K s` for `s ∈ {0, 1, c}`: the points of `AX s` other than `A`, and `Q` and one
hat point. -/
theorem ln_K [Finite P] [Finite L] (s : Row) (hs : s ≠ .ra) :
    (F.lnNb (.inr (.K s))).ncard ≤ order P L + 2 := by
  have hsub : F.lnNb (.inr (.K s)) ⊆
      Sum.inl '' ({p : P | p ∈ F.AX s} \ {F.A}) ∪
        Sum.inr '' (({NewPt.Q} : Set NewPt) ∪ NewPt.H '' {t : Row | cyc t s = true}) := by
    intro v hv
    change F.inc v (.inr (.K s)) at hv
    rcases v with p | n
    · rw [F.inc_pK] at hv
      rcases hv with ⟨h, h'⟩ | ⟨e, -⟩
      · exact Or.inl ⟨p, ⟨h, h'⟩, rfl⟩
      · exact absurd e hs
    · rcases n with _ | t
      · exact Or.inr ⟨_, Or.inl rfl, rfl⟩
      · exact Or.inr ⟨_, Or.inr ⟨t, (F.inc_HK t s).1 hv, rfl⟩, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({p : P | p ∈ F.AX s} \ {F.A}).ncard + 1 = order P L + 1 := by
    rw [ncard_diff_one (F.A_mem_AX s), ncard_points_on]
  have h3 : (({NewPt.Q} : Set NewPt) ∪ NewPt.H '' {t : Row | cyc t s = true}).ncard ≤ 2 := by
    refine (Set.ncard_union_le _ _).trans ?_
    have h4 : (NewPt.H '' {t : Row | cyc t s = true}).ncard ≤ 1 := by
      refine (Set.ncard_image_le (Set.toFinite _)).trans (ncard_le_one_of _ ?_)
      intro x hx y hy
      exact cyc_in_unique s x y hx hy
    rw [Set.ncard_singleton]
    omega
  omega

/-- Every point of the new structure has at most `q + 2` lines through it. -/
theorem point_degree [Finite P] [Finite L] (v : P ⊕ NewPt) :
    (F.ptNb v).ncard ≤ order P L + 2 := by
  rcases v with u | n
  · by_cases hA : u = F.A
    · subst hA
      exact F.pt_A
    by_cases hu : u ∈ F.ell
    · by_cases hX : ∃ t, u = F.X t
      · obtain ⟨t, rfl⟩ := hX
        by_cases ht : t = .ra
        · subst ht
          exact F.pt_Xa
        · exact F.pt_Xt t ht
      · push_neg at hX
        exact F.pt_ell u hu hX
    · exact F.pt_gen u hu hA
  · rcases n with _ | s
    · exact F.pt_Q
    · by_cases hs : s = .ra
      · subst hs
        exact F.pt_Hra
      · exact F.pt_H s hs

/-- Every line of the new structure has at most `q + 2` points on it. -/
theorem line_degree [Finite P] [Finite L] (x : L ⊕ NewLn) :
    (F.lnNb x).ncard ≤ order P L + 2 := by
  rcases x with l | n
  · by_cases hl : l = F.ell
    · subst hl
      exact F.ln_ell
    by_cases hAX : ∃ s, l = F.AX s
    · obtain ⟨s, rfl⟩ := hAX
      by_cases hs : s = .ra
      · subst hs
        exact F.ln_AXa
      · exact F.ln_AXt s hs
    · push_neg at hAX
      exact F.ln_gen l hl hAX
  · rcases n with _ | s
    · exact F.ln_M
    · by_cases hs : s = .ra
      · subst hs
        exact F.ln_Kra
      · exact F.ln_K s hs

/-- The degree bound in the graph, for every vertex. -/
theorem degree_bound [Finite P] [Finite L] (v : (P ⊕ NewPt) ⊕ (L ⊕ NewLn)) :
    (F.graph.neighborSet v).ncard ≤ order P L + 2 := by
  rcases v with p | x
  · rw [F.neighborSet_inl, Set.ncard_image_of_injective _ Sum.inr_injective]
    exact F.point_degree p
  · rw [F.neighborSet_inr, Set.ncard_image_of_injective _ Sum.inl_injective]
    exact F.line_degree x

/-- Step 1 of the proof, as counts of incident lines (points of the incidence structure). -/
theorem point_degree_card [Finite P] [Finite L] (p : P ⊕ NewPt) :
    Nat.card {l : L ⊕ NewLn // F.inc p l} ≤ order P L + 2 :=
  (Set.Nat.card_coe_set_eq (F.ptNb p)).le.trans (F.point_degree p)

/-- Step 1 of the proof, as counts of incident points (lines of the incidence structure). -/
theorem line_degree_card [Finite P] [Finite L] (x : L ⊕ NewLn) :
    Nat.card {p : P ⊕ NewPt // F.inc p x} ≤ order P L + 2 :=
  (Set.Nat.card_coe_set_eq (F.lnNb x)).le.trans (F.line_degree x)

end Frame

end BipartiteDD.Plus2
