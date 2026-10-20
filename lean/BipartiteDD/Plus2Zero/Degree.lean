import BipartiteDD.Plus2Zero.Concurrent
import BipartiteDD.Plus2.Degree

/-! Every vertex of the zero-change incidence graph has degree at most `q + 2`.

A plane point lies on `q + 1` plane lines and on at most one new line; a plane line lies on
`q + 1` plane points and on at most one new point. Each new vertex is covered by an explicit
set of plane objects, and the sizes are counted with `Set.ncard`. -/

namespace BipartiteDD.Plus2Zero
open Configuration
open BipartiteDD.Plus2 (ncard_lines_through ncard_points_on ncard_le_sum ncard_le_one_of
  ncard_diff_one)

section Counting

variable {α : Type*} [Finite α]

/-- Removing two distinct members of `T` lowers its size by two. -/
theorem ncard_sub_pair (T : Set α) {a b : α} (hab : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) :
    (T \ {a, b}).ncard + 2 = T.ncard := by
  have hsub : ({a, b} : Set α) ⊆ T := Set.insert_subset_iff.2 ⟨ha, Set.singleton_subset_iff.2 hb⟩
  rw [← Set.ncard_pair hab, Set.ncard_sdiff_add_ncard_of_subset hsub]

/-- Removing three distinct members of `T` lowers its size by three. -/
theorem ncard_sub_triple (T : Set α) {a b c : α} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T) : (T \ {a, b, c}).ncard + 3 = T.ncard := by
  have hsub : ({a, b, c} : Set α) ⊆ T :=
    Set.insert_subset_iff.2 ⟨ha, Set.insert_subset_iff.2 ⟨hb, Set.singleton_subset_iff.2 hc⟩⟩
  have h3 : ({a, b, c} : Set α).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]
  rw [← h3, Set.ncard_sdiff_add_ncard_of_subset hsub]

/-- A set with at most four listed elements has at most four elements. -/
theorem ncard_le_four (a b c d : α) : ({a, b, c, d} : Set α).ncard ≤ 4 := by
  have h1 := Set.ncard_insert_le a ({b, c, d} : Set α)
  have h2 := Set.ncard_insert_le b ({c, d} : Set α)
  have h3 := Set.ncard_insert_le c ({d} : Set α)
  have h4 := Set.ncard_singleton d
  omega

/-- A set with at most two listed elements has at most two elements. -/
theorem ncard_le_two (a b : α) : ({a, b} : Set α).ncard ≤ 2 := by
  have h1 := Set.ncard_insert_le a ({b} : Set α)
  have h2 := Set.ncard_singleton b
  omega

end Counting

namespace Frame

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]
variable (F : Frame P L)

/-! ### The incidence structure as sets -/

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
    · rintro ⟨y, hy, hyx⟩
      obtain rfl := Sum.inr_injective hyx
      exact hy

theorem neighborSet_inr (x : L ⊕ NewLn) :
    F.graph.neighborSet (.inr x) = Sum.inl '' F.lnNb x := by
  ext w
  rcases w with v | y
  · constructor
    · intro h
      exact ⟨v, h, rfl⟩
    · rintro ⟨z, hz, hzv⟩
      obtain rfl := Sum.inl_injective hzv
      exact hz
  · constructor
    · intro h
      exact absurd h (fun h' => h')
    · rintro ⟨z, _, hz⟩
      cases hz

/-! ### Old points and old lines: at most one new neighbour -/

/-- Two plane lines meet a plane point `u` and a new line each: only one new line through `u`. -/
theorem M_Ka (u : P) (h1 : F.inc (.inl u) (.inr .M)) (h2 : F.inc (.inl u) (.inr (.K .a))) :
    False := by
  obtain ⟨hℓ, -, -, -⟩ := (F.inc_pM u).1 h1
  obtain ⟨hA, hX⟩ := (F.inc_pKa u).1 h2
  exact hX ((F.mem_AX_iff .a hℓ).1 hA)

theorem M_K1 (u : P) (h1 : F.inc (.inl u) (.inr .M)) (h2 : F.inc (.inl u) (.inr (.K .one))) :
    False := by
  obtain ⟨hℓ, -, -, hX3⟩ := (F.inc_pM u).1 h1
  rcases (F.inc_pK1 u).1 h2 with ⟨hA, -, hX⟩ | h
  · exact hX ((F.mem_AX_iff .one hℓ).1 hA)
  · exact hX3 h

theorem M_K2 (u : P) (h1 : F.inc (.inl u) (.inr .M)) (h2 : F.inc (.inl u) (.inr (.K .two))) :
    False := by
  obtain ⟨hℓ, hX1, -, -⟩ := (F.inc_pM u).1 h1
  rcases (F.inc_pK2 u).1 h2 with ⟨hA, -, hX⟩ | h
  · exact hX ((F.mem_AX_iff .two hℓ).1 hA)
  · exact hX1 h

theorem M_K3 (u : P) (h1 : F.inc (.inl u) (.inr .M)) (h2 : F.inc (.inl u) (.inr (.K .three))) :
    False := by
  obtain ⟨hℓ, -, hX2, -⟩ := (F.inc_pM u).1 h1
  rcases (F.inc_pK3 u).1 h2 with ⟨hA, -, hX⟩ | h
  · exact hX ((F.mem_AX_iff .three hℓ).1 hA)
  · exact hX2 h

theorem Ka_K1 (u : P) (h1 : F.inc (.inl u) (.inr (.K .a)))
    (h2 : F.inc (.inl u) (.inr (.K .one))) : False := by
  obtain ⟨hA, -⟩ := (F.inc_pKa u).1 h1
  rcases (F.inc_pK1 u).1 h2 with ⟨hA1, hAu, -⟩ | h
  · exact hAu (F.eq_A_of_mem_AX_AX (by decide) hA hA1)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .a (F.X_mem .three)).1 hA)

theorem Ka_K2 (u : P) (h1 : F.inc (.inl u) (.inr (.K .a)))
    (h2 : F.inc (.inl u) (.inr (.K .two))) : False := by
  obtain ⟨hA, -⟩ := (F.inc_pKa u).1 h1
  rcases (F.inc_pK2 u).1 h2 with ⟨hA2, hAu, -⟩ | h
  · exact hAu (F.eq_A_of_mem_AX_AX (by decide) hA hA2)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .a (F.X_mem .one)).1 hA)

theorem Ka_K3 (u : P) (h1 : F.inc (.inl u) (.inr (.K .a)))
    (h2 : F.inc (.inl u) (.inr (.K .three))) : False := by
  obtain ⟨hA, -⟩ := (F.inc_pKa u).1 h1
  rcases (F.inc_pK3 u).1 h2 with ⟨hA3, hAu, -⟩ | h
  · exact hAu (F.eq_A_of_mem_AX_AX (by decide) hA hA3)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .a (F.X_mem .two)).1 hA)

theorem K1_K2 (u : P) (h1 : F.inc (.inl u) (.inr (.K .one)))
    (h2 : F.inc (.inl u) (.inr (.K .two))) : False := by
  rcases (F.inc_pK1 u).1 h1 with ⟨hA1, hAu1, hX1⟩ | h
  · rcases (F.inc_pK2 u).1 h2 with ⟨hA2, -, -⟩ | h
    · exact hAu1 (F.eq_A_of_mem_AX_AX (by decide) hA1 hA2)
    · exact hX1 h
  · subst h
    rcases (F.inc_pK2 _).1 h2 with ⟨hA2, -, -⟩ | h'
    · exact F.X_ne (by decide) ((F.mem_AX_iff .two (F.X_mem .three)).1 hA2)
    · exact F.X_ne (by decide) h'

theorem K1_K3 (u : P) (h1 : F.inc (.inl u) (.inr (.K .one)))
    (h2 : F.inc (.inl u) (.inr (.K .three))) : False := by
  rcases (F.inc_pK1 u).1 h1 with ⟨hA1, hAu1, hX1⟩ | h
  · rcases (F.inc_pK3 u).1 h2 with ⟨hA3, hAu3, -⟩ | h
    · exact hAu1 (F.eq_A_of_mem_AX_AX (by decide) hA1 hA3)
    · subst h
      exact F.X_ne (by decide) ((F.mem_AX_iff .one (F.X_mem .two)).1 hA1)
  · subst h
    rcases (F.inc_pK3 _).1 h2 with ⟨-, -, hX3⟩ | h'
    · exact hX3 rfl
    · exact F.X_ne (by decide) h'

theorem K2_K3 (u : P) (h1 : F.inc (.inl u) (.inr (.K .two)))
    (h2 : F.inc (.inl u) (.inr (.K .three))) : False := by
  rcases (F.inc_pK2 u).1 h1 with ⟨hA2, hAu2, hX2⟩ | h
  · rcases (F.inc_pK3 u).1 h2 with ⟨hA3, hAu3, -⟩ | h
    · exact hAu2 (F.eq_A_of_mem_AX_AX (by decide) hA2 hA3)
    · exact hX2 h
  · subst h
    rcases (F.inc_pK3 _).1 h2 with ⟨hA3, -, -⟩ | h'
    · exact F.X_ne (by decide) ((F.mem_AX_iff .three (F.X_mem .one)).1 hA3)
    · exact F.X_ne (by decide) h'

/-- An old point lies on at most one new line. -/
theorem old_pt_new_unique (u : P) : ∀ x y : NewLn,
    F.inc (.inl u) (.inr x) → F.inc (.inl u) (.inr y) → x = y
  | .M, .M, _, _ => rfl
  | .M, .K .a, hx, hy => (F.M_Ka u hx hy).elim
  | .M, .K .one, hx, hy => (F.M_K1 u hx hy).elim
  | .M, .K .two, hx, hy => (F.M_K2 u hx hy).elim
  | .M, .K .three, hx, hy => (F.M_K3 u hx hy).elim
  | .K .a, .M, hx, hy => (F.M_Ka u hy hx).elim
  | .K .a, .K .a, _, _ => rfl
  | .K .a, .K .one, hx, hy => (F.Ka_K1 u hx hy).elim
  | .K .a, .K .two, hx, hy => (F.Ka_K2 u hx hy).elim
  | .K .a, .K .three, hx, hy => (F.Ka_K3 u hx hy).elim
  | .K .one, .M, hx, hy => (F.M_K1 u hy hx).elim
  | .K .one, .K .a, hx, hy => (F.Ka_K1 u hy hx).elim
  | .K .one, .K .one, _, _ => rfl
  | .K .one, .K .two, hx, hy => (F.K1_K2 u hx hy).elim
  | .K .one, .K .three, hx, hy => (F.K1_K3 u hx hy).elim
  | .K .two, .M, hx, hy => (F.M_K2 u hy hx).elim
  | .K .two, .K .a, hx, hy => (F.Ka_K2 u hy hx).elim
  | .K .two, .K .one, hx, hy => (F.K1_K2 u hy hx).elim
  | .K .two, .K .two, _, _ => rfl
  | .K .two, .K .three, hx, hy => (F.K2_K3 u hx hy).elim
  | .K .three, .M, hx, hy => (F.M_K3 u hy hx).elim
  | .K .three, .K .a, hx, hy => (F.Ka_K3 u hy hx).elim
  | .K .three, .K .one, hx, hy => (F.K1_K3 u hy hx).elim
  | .K .three, .K .two, hx, hy => (F.K2_K3 u hy hx).elim
  | .K .three, .K .three, _, _ => rfl

/-- Two distinct points of `ℓ`'s hats are on `ℓ`, so a line through both is `ℓ`. -/
theorem eq_ell_of {l : L} {p q : P} (hpq : p ≠ q) (hp : p ∈ F.ell) (hq : q ∈ F.ell)
    (hpl : p ∈ l) (hql : q ∈ l) : l = F.ell :=
  (Nondegenerate.eq_or_eq hpl hql hp hq).resolve_left hpq

theorem Q_Ha (l : L) (h1 : F.inc (.inr .Q) (.inl l)) (h2 : F.inc (.inr (.H .a)) (.inl l)) :
    False := by
  obtain ⟨hA, -, -, -⟩ := (F.inc_Ql l).1 h1
  obtain ⟨hXa, hna⟩ := (F.inc_Ha l).1 h2
  exact hna (F.eq_AX_of_mem .a hA hXa)

theorem Q_H1 (l : L) (h1 : F.inc (.inr .Q) (.inl l)) (h2 : F.inc (.inr (.H .one)) (.inl l)) :
    False := by
  obtain ⟨hA, -, hn2, -⟩ := (F.inc_Ql l).1 h1
  rcases (F.inc_H1 l).1 h2 with ⟨hX1, -, hna⟩ | h
  · exact hna (F.eq_AX_of_mem .one hA hX1)
  · exact hn2 h

theorem Q_H2 (l : L) (h1 : F.inc (.inr .Q) (.inl l)) (h2 : F.inc (.inr (.H .two)) (.inl l)) :
    False := by
  obtain ⟨hA, -, -, hn3⟩ := (F.inc_Ql l).1 h1
  rcases (F.inc_H2 l).1 h2 with ⟨hX2, -, hna⟩ | h
  · exact hna (F.eq_AX_of_mem .two hA hX2)
  · exact hn3 h

theorem Q_H3 (l : L) (h1 : F.inc (.inr .Q) (.inl l)) (h2 : F.inc (.inr (.H .three)) (.inl l)) :
    False := by
  obtain ⟨hA, hn1, -, -⟩ := (F.inc_Ql l).1 h1
  rcases (F.inc_H3 l).1 h2 with ⟨hX3, -, hna⟩ | h
  · exact hna (F.eq_AX_of_mem .three hA hX3)
  · exact hn1 h

theorem Ha_H1 (l : L) (h1 : F.inc (.inr (.H .a)) (.inl l)) (h2 : F.inc (.inr (.H .one)) (.inl l)) :
    False := by
  obtain ⟨hXa, hna⟩ := (F.inc_Ha l).1 h1
  rcases (F.inc_H1 l).1 h2 with ⟨hX1, hℓ, -⟩ | h
  · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .a) (F.X_mem .one) hXa hX1)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .two (F.X_mem .a)).1 hXa)

theorem Ha_H2 (l : L) (h1 : F.inc (.inr (.H .a)) (.inl l)) (h2 : F.inc (.inr (.H .two)) (.inl l)) :
    False := by
  obtain ⟨hXa, hna⟩ := (F.inc_Ha l).1 h1
  rcases (F.inc_H2 l).1 h2 with ⟨hX2, hℓ, -⟩ | h
  · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .a) (F.X_mem .two) hXa hX2)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .three (F.X_mem .a)).1 hXa)

theorem Ha_H3 (l : L) (h1 : F.inc (.inr (.H .a)) (.inl l)) (h2 : F.inc (.inr (.H .three)) (.inl l)) :
    False := by
  obtain ⟨hXa, hna⟩ := (F.inc_Ha l).1 h1
  rcases (F.inc_H3 l).1 h2 with ⟨hX3, hℓ, -⟩ | h
  · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .a) (F.X_mem .three) hXa hX3)
  · subst h
    exact F.X_ne (by decide) ((F.mem_AX_iff .one (F.X_mem .a)).1 hXa)

theorem H1_H2 (l : L) (h1 : F.inc (.inr (.H .one)) (.inl l)) (h2 : F.inc (.inr (.H .two)) (.inl l)) :
    False := by
  rcases (F.inc_H1 l).1 h1 with ⟨hX1, hℓ, -⟩ | h
  · rcases (F.inc_H2 l).1 h2 with ⟨hX2, -, -⟩ | h
    · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .one) (F.X_mem .two) hX1 hX2)
    · subst h
      exact F.X_ne (by decide) ((F.mem_AX_iff .three (F.X_mem .one)).1 hX1)
  · subst h
    rcases (F.inc_H2 (F.AX .two)).1 h2 with ⟨-, -, hn2⟩ | h'
    · exact hn2 rfl
    · exact F.AX_ne (by decide) h'

theorem H1_H3 (l : L) (h1 : F.inc (.inr (.H .one)) (.inl l)) (h2 : F.inc (.inr (.H .three)) (.inl l)) :
    False := by
  rcases (F.inc_H1 l).1 h1 with ⟨hX1, hℓ, hn1⟩ | h
  · rcases (F.inc_H3 l).1 h2 with ⟨hX3, -, -⟩ | h'
    · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .one) (F.X_mem .three) hX1 hX3)
    · subst h'
      exact hn1 rfl
  · subst h
    rcases (F.inc_H3 (F.AX .two)).1 h2 with ⟨hX3, -, -⟩ | h'
    · exact F.X_ne (by decide) ((F.mem_AX_iff .two (F.X_mem .three)).1 hX3)
    · exact F.AX_ne (by decide) h'

theorem H2_H3 (l : L) (h1 : F.inc (.inr (.H .two)) (.inl l)) (h2 : F.inc (.inr (.H .three)) (.inl l)) :
    False := by
  rcases (F.inc_H2 l).1 h1 with ⟨hX2, hℓ, hn2⟩ | h
  · rcases (F.inc_H3 l).1 h2 with ⟨hX3, -, -⟩ | h'
    · exact hℓ (F.eq_ell_of (F.X_ne (by decide)) (F.X_mem .two) (F.X_mem .three) hX2 hX3)
    · subst h'
      exact F.X_ne (by decide) ((F.mem_AX_iff .one (F.X_mem .two)).1 hX2)
  · subst h
    rcases (F.inc_H3 (F.AX .three)).1 h2 with ⟨-, -, hn3⟩ | h'
    · exact hn3 rfl
    · exact F.AX_ne (by decide) h'

/-- A plane line carries at most one new point. -/
theorem old_line_new_unique (l : L) : ∀ x y : NewPt,
    F.inc (.inr x) (.inl l) → F.inc (.inr y) (.inl l) → x = y
  | .Q, .Q, _, _ => rfl
  | .Q, .H .a, hx, hy => (F.Q_Ha l hx hy).elim
  | .Q, .H .one, hx, hy => (F.Q_H1 l hx hy).elim
  | .Q, .H .two, hx, hy => (F.Q_H2 l hx hy).elim
  | .Q, .H .three, hx, hy => (F.Q_H3 l hx hy).elim
  | .H .a, .Q, hx, hy => (F.Q_Ha l hy hx).elim
  | .H .a, .H .a, _, _ => rfl
  | .H .a, .H .one, hx, hy => (F.Ha_H1 l hx hy).elim
  | .H .a, .H .two, hx, hy => (F.Ha_H2 l hx hy).elim
  | .H .a, .H .three, hx, hy => (F.Ha_H3 l hx hy).elim
  | .H .one, .Q, hx, hy => (F.Q_H1 l hy hx).elim
  | .H .one, .H .a, hx, hy => (F.Ha_H1 l hy hx).elim
  | .H .one, .H .one, _, _ => rfl
  | .H .one, .H .two, hx, hy => (F.H1_H2 l hx hy).elim
  | .H .one, .H .three, hx, hy => (F.H1_H3 l hx hy).elim
  | .H .two, .Q, hx, hy => (F.Q_H2 l hy hx).elim
  | .H .two, .H .a, hx, hy => (F.Ha_H2 l hy hx).elim
  | .H .two, .H .one, hx, hy => (F.H1_H2 l hy hx).elim
  | .H .two, .H .two, _, _ => rfl
  | .H .two, .H .three, hx, hy => (F.H2_H3 l hx hy).elim
  | .H .three, .Q, hx, hy => (F.Q_H3 l hy hx).elim
  | .H .three, .H .a, hx, hy => (F.Ha_H3 l hy hx).elim
  | .H .three, .H .one, hx, hy => (F.H1_H3 l hy hx).elim
  | .H .three, .H .two, hx, hy => (F.H2_H3 l hy hx).elim
  | .H .three, .H .three, _, _ => rfl

/-! ### Degrees of points -/

/-- A plane point has `q + 1` plane lines through it and at most one new line. -/
theorem deg_old_pt (u : P) : (F.ptNb (.inl u)).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inl u) ⊆
      Sum.inl '' {l : L | u ∈ l} ∪ Sum.inr '' {x : NewLn | F.inc (.inl u) (.inr x)} := by
    intro x hx
    change F.inc (.inl u) x at hx
    rcases x with l | n
    · exact Or.inl ⟨l, (F.inc_pp u l).1 hx, rfl⟩
    · exact Or.inr ⟨n, hx, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({x : NewLn | F.inc (.inl u) (.inr x)}).ncard ≤ 1 :=
    ncard_le_one_of _ (fun x hx y hy => F.old_pt_new_unique u x y hx hy)
  rw [ncard_lines_through] at h1
  omega

/-- `Q` sees the lines through `A` except three, and the four hat lines. -/
theorem deg_Q : (F.ptNb (.inr .Q)).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inr .Q) ⊆
      Sum.inl '' ({l : L | F.A ∈ l} \ {F.AX .one, F.AX .two, F.AX .three}) ∪
        Sum.inr '' ({.K .a, .K .one, .K .two, .K .three} : Set NewLn) := by
    intro x hx
    change F.inc (.inr .Q) x at hx
    rcases x with l | n
    · obtain ⟨hA, h1, h2, h3⟩ := (F.inc_Ql l).1 hx
      exact Or.inl ⟨l, Set.mem_sdiff_of_mem hA (by simp [h1, h2, h3]), rfl⟩
    · rcases n with _ | h
      · exact absurd hx F.not_inc_QM
      · exact Or.inr ⟨.K h, by rcases h with _ | _ | _ | _ <;> simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_triple {l : L | F.A ∈ l} (F.AX_ne (by decide)) (F.AX_ne (by decide))
    (F.AX_ne (by decide)) (F.A_mem_AX .one) (F.A_mem_AX .two) (F.A_mem_AX .three)
  have h3 := ncard_le_four (NewLn.K .a) (.K .one) (.K .two) (.K .three)
  have h4 : ({l : L | F.A ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through F.A
  omega

/-- A plane line has `q + 1` plane points on it and at most one new point. -/
theorem deg_old_ln (l : L) : (F.lnNb (.inl l)).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inl l) ⊆
      Sum.inl '' {p : P | p ∈ l} ∪ Sum.inr '' {n : NewPt | F.inc (.inr n) (.inl l)} := by
    intro v hv
    change F.inc v (.inl l) at hv
    rcases v with p | n
    · exact Or.inl ⟨p, (F.inc_pp p l).1 hv, rfl⟩
    · exact Or.inr ⟨n, hv, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 : ({n : NewPt | F.inc (.inr n) (.inl l)}).ncard ≤ 1 :=
    ncard_le_one_of _ (fun x hx y hy => F.old_line_new_unique l x y hx hy)
  have h3 : ({p : P | p ∈ l}).ncard = ProjectivePlane.order P L + 1 := ncard_points_on l
  omega

/-- `M` sees the points of `ℓ` other than the three feet, and the four copies `H h`. -/
theorem deg_M : (F.lnNb (.inr .M)).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inr .M) ⊆
      Sum.inl '' ({p : P | p ∈ F.ell} \ {F.X .one, F.X .two, F.X .three}) ∪
        Sum.inr '' ({.H .a, .H .one, .H .two, .H .three} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr .M) at hv
    rcases v with p | n
    · obtain ⟨hℓ, h1, h2, h3⟩ := (F.inc_pM p).1 hv
      exact Or.inl ⟨p, Set.mem_sdiff_of_mem hℓ (by simp [h1, h2, h3]), rfl⟩
    · rcases n with _ | h
      · exact absurd hv F.not_inc_QM
      · exact Or.inr ⟨.H h, by rcases h with _ | _ | _ | _ <;> simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_triple {p : P | p ∈ F.ell} (a := F.X .one) (b := F.X .two)
    (c := F.X .three) (F.X_ne (by decide)) (F.X_ne (by decide)) (F.X_ne (by decide))
    (F.X_mem .one) (F.X_mem .two) (F.X_mem .three)
  have h3 := ncard_le_four (NewPt.H .a) (.H .one) (.H .two) (.H .three)
  have h4 : ({p : P | p ∈ F.ell}).ncard = ProjectivePlane.order P L + 1 := ncard_points_on F.ell
  omega

/-- `H a` sees the lines through `X a` other than `AX a`, and `M`, `K a`. -/
theorem deg_Ha : (F.ptNb (.inr (.H .a))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inr (.H .a)) ⊆
      Sum.inl '' ({l : L | F.X .a ∈ l} \ {F.AX .a}) ∪ Sum.inr '' ({.M, .K .a} : Set NewLn) := by
    intro x hx
    change F.inc (.inr (.H .a)) x at hx
    rcases x with l | n
    · obtain ⟨hX, hn⟩ := (F.inc_Ha l).1 hx
      exact Or.inl ⟨l, Set.mem_sdiff_of_mem hX (by simp [hn]), rfl⟩
    · rcases n with _ | k
      · exact Or.inr ⟨.M, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hx
        exact Or.inr ⟨.K .a, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_diff_one (S := {l : L | F.X .a ∈ l}) (a := F.AX .a) (F.X_mem_AX .a)
  have h3 := ncard_le_two (NewLn.M) (NewLn.K .a)
  have h4 : ({l : L | F.X .a ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .a)
  omega

/-- `H one` sees the lines through `X one` other than `ℓ` and `AX one`, the line `AX two`,
and `M`, `K one`. -/
theorem deg_H1 : (F.ptNb (.inr (.H .one))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inr (.H .one)) ⊆
      Sum.inl '' (({l : L | F.X .one ∈ l} \ {F.ell, F.AX .one}) ∪ {F.AX .two}) ∪
        Sum.inr '' ({.M, .K .one} : Set NewLn) := by
    intro x hx
    change F.inc (.inr (.H .one)) x at hx
    rcases x with l | n
    · rcases (F.inc_H1 l).1 hx with ⟨hX, hℓ, hn⟩ | h
      · exact Or.inl ⟨l, Set.mem_union_left _ (Set.mem_sdiff_of_mem hX (by simp [hℓ, hn])), rfl⟩
      · exact Or.inl ⟨l, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | k
      · exact Or.inr ⟨.M, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hx
        exact Or.inr ⟨.K .one, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {l : L | F.X .one ∈ l} (a := F.ell) (b := F.AX .one)
    (F.AX_ne_ell .one).symm (F.X_mem .one) (F.X_mem_AX .one)
  have h3 := Set.ncard_union_le ({l : L | F.X .one ∈ l} \ {F.ell, F.AX .one}) {F.AX .two}
  have h4 := Set.ncard_singleton (F.AX .two)
  have h5 := ncard_le_two (NewLn.M) (NewLn.K .one)
  have h6 : ({l : L | F.X .one ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .one)
  omega

/-- `H two` sees the lines through `X two` other than `ℓ` and `AX two`, the line `AX three`,
and `M`, `K two`. -/
theorem deg_H2 : (F.ptNb (.inr (.H .two))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inr (.H .two)) ⊆
      Sum.inl '' (({l : L | F.X .two ∈ l} \ {F.ell, F.AX .two}) ∪ {F.AX .three}) ∪
        Sum.inr '' ({.M, .K .two} : Set NewLn) := by
    intro x hx
    change F.inc (.inr (.H .two)) x at hx
    rcases x with l | n
    · rcases (F.inc_H2 l).1 hx with ⟨hX, hℓ, hn⟩ | h
      · exact Or.inl ⟨l, Set.mem_union_left _ (Set.mem_sdiff_of_mem hX (by simp [hℓ, hn])), rfl⟩
      · exact Or.inl ⟨l, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | k
      · exact Or.inr ⟨.M, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hx
        exact Or.inr ⟨.K .two, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {l : L | F.X .two ∈ l} (a := F.ell) (b := F.AX .two)
    (F.AX_ne_ell .two).symm (F.X_mem .two) (F.X_mem_AX .two)
  have h3 := Set.ncard_union_le ({l : L | F.X .two ∈ l} \ {F.ell, F.AX .two}) {F.AX .three}
  have h4 := Set.ncard_singleton (F.AX .three)
  have h5 := ncard_le_two (NewLn.M) (NewLn.K .two)
  have h6 : ({l : L | F.X .two ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .two)
  omega

/-- `H three` sees the lines through `X three` other than `ℓ` and `AX three`, the line `AX one`,
and `M`, `K three`. -/
theorem deg_H3 : (F.ptNb (.inr (.H .three))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.ptNb (.inr (.H .three)) ⊆
      Sum.inl '' (({l : L | F.X .three ∈ l} \ {F.ell, F.AX .three}) ∪ {F.AX .one}) ∪
        Sum.inr '' ({.M, .K .three} : Set NewLn) := by
    intro x hx
    change F.inc (.inr (.H .three)) x at hx
    rcases x with l | n
    · rcases (F.inc_H3 l).1 hx with ⟨hX, hℓ, hn⟩ | h
      · exact Or.inl ⟨l, Set.mem_union_left _ (Set.mem_sdiff_of_mem hX (by simp [hℓ, hn])), rfl⟩
      · exact Or.inl ⟨l, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | k
      · exact Or.inr ⟨.M, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hx
        exact Or.inr ⟨.K .three, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {l : L | F.X .three ∈ l} (a := F.ell) (b := F.AX .three)
    (F.AX_ne_ell .three).symm (F.X_mem .three) (F.X_mem_AX .three)
  have h3 := Set.ncard_union_le ({l : L | F.X .three ∈ l} \ {F.ell, F.AX .three}) {F.AX .one}
  have h4 := Set.ncard_singleton (F.AX .one)
  have h5 := ncard_le_two (NewLn.M) (NewLn.K .three)
  have h6 : ({l : L | F.X .three ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .three)
  omega

/-- `K a` sees the points of `AX a` other than `X a`, and `Q`, `H a`. -/
theorem deg_Ka : (F.lnNb (.inr (.K .a))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inr (.K .a)) ⊆
      Sum.inl '' ({p : P | p ∈ F.AX .a} \ {F.X .a}) ∪ Sum.inr '' ({.Q, .H .a} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr (.K .a)) at hv
    rcases v with p | n
    · obtain ⟨hp, hne⟩ := (F.inc_pKa p).1 hv
      exact Or.inl ⟨p, Set.mem_sdiff_of_mem hp (by simp [hne]), rfl⟩
    · rcases n with _ | h
      · exact Or.inr ⟨.Q, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hv
        exact Or.inr ⟨.H .a, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_diff_one (S := {p : P | p ∈ F.AX .a}) (a := F.X .a) (F.X_mem_AX .a)
  have h3 := ncard_le_two (NewPt.Q) (NewPt.H .a)
  have h4 : ({p : P | p ∈ F.AX .a}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .a)
  omega

/-- `K one` sees the points of `AX one` other than `A` and `X one`, the point `X three`, and
`Q`, `H one`. -/
theorem deg_K1 : (F.lnNb (.inr (.K .one))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inr (.K .one)) ⊆
      Sum.inl '' (({p : P | p ∈ F.AX .one} \ {F.A, F.X .one}) ∪ {F.X .three}) ∪
        Sum.inr '' ({.Q, .H .one} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr (.K .one)) at hv
    rcases v with p | n
    · rcases (F.inc_pK1 p).1 hv with ⟨hp, hA, hX⟩ | h
      · exact Or.inl ⟨p, Set.mem_union_left _ (Set.mem_sdiff_of_mem hp (by simp [hA, hX])), rfl⟩
      · exact Or.inl ⟨p, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | h
      · exact Or.inr ⟨.Q, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hv
        exact Or.inr ⟨.H .one, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {p : P | p ∈ F.AX .one} (a := F.A) (b := F.X .one)
    (F.A_ne_X .one) (F.A_mem_AX .one) (F.X_mem_AX .one)
  have h3 := Set.ncard_union_le ({p : P | p ∈ F.AX .one} \ {F.A, F.X .one}) {F.X .three}
  have h4 := Set.ncard_singleton (F.X .three)
  have h5 := ncard_le_two (NewPt.Q) (NewPt.H .one)
  have h6 : ({p : P | p ∈ F.AX .one}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .one)
  omega

/-- `K two` sees the points of `AX two` other than `A` and `X two`, the point `X one`, and
`Q`, `H two`. -/
theorem deg_K2 : (F.lnNb (.inr (.K .two))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inr (.K .two)) ⊆
      Sum.inl '' (({p : P | p ∈ F.AX .two} \ {F.A, F.X .two}) ∪ {F.X .one}) ∪
        Sum.inr '' ({.Q, .H .two} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr (.K .two)) at hv
    rcases v with p | n
    · rcases (F.inc_pK2 p).1 hv with ⟨hp, hA, hX⟩ | h
      · exact Or.inl ⟨p, Set.mem_union_left _ (Set.mem_sdiff_of_mem hp (by simp [hA, hX])), rfl⟩
      · exact Or.inl ⟨p, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | h
      · exact Or.inr ⟨.Q, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hv
        exact Or.inr ⟨.H .two, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {p : P | p ∈ F.AX .two} (a := F.A) (b := F.X .two)
    (F.A_ne_X .two) (F.A_mem_AX .two) (F.X_mem_AX .two)
  have h3 := Set.ncard_union_le ({p : P | p ∈ F.AX .two} \ {F.A, F.X .two}) {F.X .one}
  have h4 := Set.ncard_singleton (F.X .one)
  have h5 := ncard_le_two (NewPt.Q) (NewPt.H .two)
  have h6 : ({p : P | p ∈ F.AX .two}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .two)
  omega

/-- `K three` sees the points of `AX three` other than `A` and `X three`, the point `X two`, and
`Q`, `H three`. -/
theorem deg_K3 : (F.lnNb (.inr (.K .three))).ncard ≤ ProjectivePlane.order P L + 2 := by
  have hsub : F.lnNb (.inr (.K .three)) ⊆
      Sum.inl '' (({p : P | p ∈ F.AX .three} \ {F.A, F.X .three}) ∪ {F.X .two}) ∪
        Sum.inr '' ({.Q, .H .three} : Set NewPt) := by
    intro v hv
    change F.inc v (.inr (.K .three)) at hv
    rcases v with p | n
    · rcases (F.inc_pK3 p).1 hv with ⟨hp, hA, hX⟩ | h
      · exact Or.inl ⟨p, Set.mem_union_left _ (Set.mem_sdiff_of_mem hp (by simp [hA, hX])), rfl⟩
      · exact Or.inl ⟨p, Set.mem_union_right _ (Set.mem_singleton_iff.2 h), rfl⟩
    · rcases n with _ | h
      · exact Or.inr ⟨.Q, by simp, rfl⟩
      · obtain rfl := (F.inc_HK _ _).1 hv
        exact Or.inr ⟨.H .three, by simp, rfl⟩
  have h1 := ncard_le_sum _ _ _ hsub
  have h2 := ncard_sub_pair {p : P | p ∈ F.AX .three} (a := F.A) (b := F.X .three)
    (F.A_ne_X .three) (F.A_mem_AX .three) (F.X_mem_AX .three)
  have h3 := Set.ncard_union_le ({p : P | p ∈ F.AX .three} \ {F.A, F.X .three}) {F.X .two}
  have h4 := Set.ncard_singleton (F.X .two)
  have h5 := ncard_le_two (NewPt.Q) (NewPt.H .three)
  have h6 : ({p : P | p ∈ F.AX .three}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .three)
  omega

/-- Every point of the new structure has at most `q + 2` lines through it. -/
theorem point_degree (v : P ⊕ NewPt) : (F.ptNb v).ncard ≤ ProjectivePlane.order P L + 2 := by
  rcases v with u | n
  · exact F.deg_old_pt u
  · rcases n with _ | h
    · exact F.deg_Q
    · rcases h with _ | _ | _ | _
      · exact F.deg_Ha
      · exact F.deg_H1
      · exact F.deg_H2
      · exact F.deg_H3

/-- Every line of the new structure has at most `q + 2` points on it. -/
theorem line_degree (x : L ⊕ NewLn) : (F.lnNb x).ncard ≤ ProjectivePlane.order P L + 2 := by
  rcases x with l | n
  · exact F.deg_old_ln l
  · rcases n with _ | h
    · exact F.deg_M
    · rcases h with _ | _ | _ | _
      · exact F.deg_Ka
      · exact F.deg_K1
      · exact F.deg_K2
      · exact F.deg_K3

/-- The degree bound in the graph, for every vertex. -/
theorem degree_bound (v : (P ⊕ NewPt) ⊕ (L ⊕ NewLn)) :
    (F.graph.neighborSet v).ncard ≤ ProjectivePlane.order P L + 2 := by
  rcases v with p | x
  · rw [F.neighborSet_inl, Set.ncard_image_of_injective _ Sum.inr_injective]
    exact F.point_degree p
  · rw [F.neighborSet_inr, Set.ncard_image_of_injective _ Sum.inl_injective]
    exact F.line_degree x

end Frame

end BipartiteDD.Plus2Zero
