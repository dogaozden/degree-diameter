import BipartiteDD.Plus2Zero.Exists
import BipartiteDD.Regular.Completion

/-! Target 3: the regular version. Every vertex of the zero-change graph has at most `q + 2`
neighbours (`Degree.lean`). A vertex has at least `q + 1`: a plane vertex has its `q + 1` plane
neighbours, and a new vertex has an explicit set of at least `q + 1` neighbours. A plane point
is deficient when no new line passes through it, and then it has exactly `q + 1` neighbours. The
deficient points number at least `q² - 4q + 3`, which exceeds `2 (q + 4)` once `q ≥ 7`, so the
generic completion lemma `BipartiteDD.Regular.exists_regular_completion_fin` (with `s = 1`) gives
a `(q + 2)`-regular bipartite graph of diameter at most `3`. -/

namespace BipartiteDD.Plus2Zero
open Configuration
open BipartiteDD.Plus2 (ncard_lines_through ncard_points_on ncard_diff_one)

section Generic

variable {α β : Type*} [Finite α] [Finite β]

/-- Neighbours on both sides add up: a set of `α`-vertices and a set of `β`-vertices, all
adjacent to a common vertex, contribute their sizes to its degree. -/
theorem ncard_sum_le (S : Set α) (T : Set β) (N : Set (α ⊕ β))
    (h : Sum.inl '' S ∪ Sum.inr '' T ⊆ N) : S.ncard + T.ncard ≤ N.ncard := by
  have hdisj : Disjoint (Sum.inl '' S) (Sum.inr '' T) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, -, rfl⟩ ⟨b, -, hb⟩
    cases hb
  calc S.ncard + T.ncard = (Sum.inl '' S).ncard + (Sum.inr '' T).ncard := by
        rw [Set.ncard_image_of_injective _ Sum.inl_injective,
          Set.ncard_image_of_injective _ Sum.inr_injective]
    _ = (Sum.inl '' S ∪ Sum.inr '' T).ncard := (Set.ncard_union_eq hdisj).symm
    _ ≤ N.ncard := Set.ncard_le_ncard h (Set.toFinite _)

end Generic

section Counting

variable {α : Type*} [Finite α]

/-- Three distinct elements form a set of size three. -/
theorem ncard_three_eq (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Set α).ncard = 3 := by
  rw [Set.ncard_insert_of_notMem (by simp [hab, hac]), Set.ncard_pair hbc]

/-- A set of size at least `k` in which every element of a finite type is counted: a set of
`Fintype` elements has at most as many members as the sum of a non-negative weight that is at
least one on it. -/
theorem sum_ge_ncard {γ : Type*} [Fintype γ] (D : Set γ) (g : γ → ℕ)
    (hg : ∀ u ∈ D, 1 ≤ g u) : D.ncard ≤ ∑ u, g u := by
  classical
  have h1 : D.ncard = (Finset.univ.filter (· ∈ D)).card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp
  rw [h1, Finset.card_filter]
  apply Finset.sum_le_sum
  intro u _
  by_cases h : u ∈ D
  · simp only [h, if_true]
    exact hg u h
  · simp [h]

end Counting

namespace Frame

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Finite P] [Finite L]
variable (F : Frame P L)

theorem graph_eq_biGraph : F.graph = BipartiteDD.Regular.biGraph F.inc := by
  ext u v
  rcases u with p | l <;> rcases v with q | m <;> exact Iff.rfl

/-! ### Lower bounds: every vertex has at least `q + 1` neighbours -/

/-- A plane point has its `q + 1` plane lines. -/
theorem lb_old_pt (u : P) : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inl u)).ncard := by
  have hsub : Sum.inl '' {l : L | u ∈ l} ⊆ F.ptNb (.inl u) := by
    rintro _ ⟨l, hl, rfl⟩
    exact (F.inc_pp u l).2 hl
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_lines_through] at h
  exact h

/-- A plane line has its `q + 1` plane points. -/
theorem lb_old_ln (l : L) : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inl l)).ncard := by
  have hsub : Sum.inl '' {p : P | p ∈ l} ⊆ F.lnNb (.inl l) := by
    rintro _ ⟨p, hp, rfl⟩
    exact (F.inc_pp p l).2 hp
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_points_on] at h
  exact h

theorem lb_Q : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inr .Q)).ncard := by
  have hT : ({NewLn.K .a, .K .one, .K .two} : Set NewLn).ncard = 3 :=
    ncard_three_eq _ _ _ (by decide) (by decide) (by decide)
  have hS := ncard_sub_triple {l : L | F.A ∈ l} (a := F.AX .one) (b := F.AX .two)
    (c := F.AX .three) (F.AX_ne (by decide)) (F.AX_ne (by decide)) (F.AX_ne (by decide))
    (F.A_mem_AX .one) (F.A_mem_AX .two) (F.A_mem_AX .three)
  have hN : ({l : L | F.A ∈ l}).ncard = ProjectivePlane.order P L + 1 := ncard_lines_through F.A
  have h := ncard_sum_le ({l : L | F.A ∈ l} \ {F.AX .one, F.AX .two, F.AX .three})
    ({NewLn.K .a, .K .one, .K .two} : Set NewLn) (F.ptNb (.inr .Q)) (by
      rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hA, hn'⟩ := hl
        have h1 : l ≠ F.AX .one := fun e => hn' (by simp [e])
        have h2 : l ≠ F.AX .two := fun e => hn' (by simp [e])
        have h3 : l ≠ F.AX .three := fun e => hn' (by simp [e])
        exact (F.inc_Ql l).2 ⟨hA, h1, h2, h3⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl | rfl
        · exact F.inc_QK .a
        · exact F.inc_QK .one
        · exact F.inc_QK .two)
  omega

theorem lb_Ha : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inr (.H .a))).ncard := by
  have hS := ncard_diff_one (S := {l : L | F.X .a ∈ l}) (a := F.AX .a) (F.X_mem_AX .a)
  have hN : ({l : L | F.X .a ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .a)
  have h := ncard_sum_le ({l : L | F.X .a ∈ l} \ {F.AX .a}) ({NewLn.M} : Set NewLn)
    (F.ptNb (.inr (.H .a))) (by
      rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hX, hn'⟩ := hl
        have h1 : l ≠ F.AX .a := fun e => hn' (by simp [e])
        exact (F.inc_Ha l).2 ⟨hX, h1⟩
      · simp only [Set.mem_singleton_iff] at hn
        rcases hn with rfl
        exact F.inc_HM .a)
  rw [Set.ncard_singleton] at h
  omega

theorem lb_H1 : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inr (.H .one))).ncard := by
  have hS := ncard_sub_pair {l : L | F.X .one ∈ l} (a := F.ell) (b := F.AX .one)
    (F.AX_ne_ell .one).symm (F.X_mem .one) (F.X_mem_AX .one)
  have hN : ({l : L | F.X .one ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .one)
  have hT : ({NewLn.M, NewLn.K .one} : Set NewLn).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({l : L | F.X .one ∈ l} \ {F.ell, F.AX .one})
    ({NewLn.M, NewLn.K .one} : Set NewLn) (F.ptNb (.inr (.H .one))) (by
      rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hX, hn'⟩ := hl
        have h1 : l ≠ F.ell := fun e => hn' (by simp [e])
        have h2 : l ≠ F.AX .one := fun e => hn' (by simp [e])
        exact (F.inc_H1 l).2 (Or.inl ⟨hX, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_HM .one
        · exact (F.inc_HK .one .one).2 rfl)
  omega

theorem lb_H2 : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inr (.H .two))).ncard := by
  have hS := ncard_sub_pair {l : L | F.X .two ∈ l} (a := F.ell) (b := F.AX .two)
    (F.AX_ne_ell .two).symm (F.X_mem .two) (F.X_mem_AX .two)
  have hN : ({l : L | F.X .two ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .two)
  have hT : ({NewLn.M, NewLn.K .two} : Set NewLn).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({l : L | F.X .two ∈ l} \ {F.ell, F.AX .two})
    ({NewLn.M, NewLn.K .two} : Set NewLn) (F.ptNb (.inr (.H .two))) (by
      rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hX, hn'⟩ := hl
        have h1 : l ≠ F.ell := fun e => hn' (by simp [e])
        have h2 : l ≠ F.AX .two := fun e => hn' (by simp [e])
        exact (F.inc_H2 l).2 (Or.inl ⟨hX, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_HM .two
        · exact (F.inc_HK .two .two).2 rfl)
  omega

theorem lb_H3 : ProjectivePlane.order P L + 1 ≤ (F.ptNb (.inr (.H .three))).ncard := by
  have hS := ncard_sub_pair {l : L | F.X .three ∈ l} (a := F.ell) (b := F.AX .three)
    (F.AX_ne_ell .three).symm (F.X_mem .three) (F.X_mem_AX .three)
  have hN : ({l : L | F.X .three ∈ l}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_lines_through (F.X .three)
  have hT : ({NewLn.M, NewLn.K .three} : Set NewLn).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({l : L | F.X .three ∈ l} \ {F.ell, F.AX .three})
    ({NewLn.M, NewLn.K .three} : Set NewLn) (F.ptNb (.inr (.H .three))) (by
      rintro x (⟨l, hl, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hX, hn'⟩ := hl
        have h1 : l ≠ F.ell := fun e => hn' (by simp [e])
        have h2 : l ≠ F.AX .three := fun e => hn' (by simp [e])
        exact (F.inc_H3 l).2 (Or.inl ⟨hX, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_HM .three
        · exact (F.inc_HK .three .three).2 rfl)
  omega

/-- The lower bound for every point of the new structure. -/
theorem lb_pt (v : P ⊕ NewPt) : ProjectivePlane.order P L + 1 ≤ (F.ptNb v).ncard := by
  rcases v with u | n
  · exact F.lb_old_pt u
  · rcases n with _ | h
    · exact F.lb_Q
    · rcases h with _ | _ | _ | _
      · exact F.lb_Ha
      · exact F.lb_H1
      · exact F.lb_H2
      · exact F.lb_H3

theorem lb_M : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inr .M)).ncard := by
  have hS := ncard_sub_triple {p : P | p ∈ F.ell} (a := F.X .one) (b := F.X .two)
    (c := F.X .three) (F.X_ne (by decide)) (F.X_ne (by decide)) (F.X_ne (by decide))
    (F.X_mem .one) (F.X_mem .two) (F.X_mem .three)
  have hN : ({p : P | p ∈ F.ell}).ncard = ProjectivePlane.order P L + 1 := ncard_points_on F.ell
  have hT := ncard_three_eq (NewPt.H .a) (.H .one) (.H .two) (by decide) (by decide) (by decide)
  have h := ncard_sum_le ({p : P | p ∈ F.ell} \ {F.X .one, F.X .two, F.X .three})
    ({NewPt.H .a, .H .one, .H .two} : Set NewPt) (F.lnNb (.inr .M)) (by
      rintro x (⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hℓ, hn'⟩ := hp
        have h1 : p ≠ F.X .one := fun e => hn' (by simp [e])
        have h2 : p ≠ F.X .two := fun e => hn' (by simp [e])
        have h3 : p ≠ F.X .three := fun e => hn' (by simp [e])
        exact (F.inc_pM p).2 ⟨hℓ, h1, h2, h3⟩
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl | rfl
        · exact F.inc_HM .a
        · exact F.inc_HM .one
        · exact F.inc_HM .two)
  omega

theorem lb_Ka : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inr (.K .a))).ncard := by
  have hS := ncard_diff_one (S := {p : P | p ∈ F.AX .a}) (a := F.X .a) (F.X_mem_AX .a)
  have hN : ({p : P | p ∈ F.AX .a}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .a)
  have hT : ({NewPt.Q} : Set NewPt).ncard = 1 := Set.ncard_singleton _
  have h := ncard_sum_le ({p : P | p ∈ F.AX .a} \ {F.X .a}) ({NewPt.Q} : Set NewPt)
    (F.lnNb (.inr (.K .a))) (by
      rintro x (⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hA, hn'⟩ := hp
        have h1 : p ≠ F.X .a := fun e => hn' (by simp [e])
        exact (F.inc_pKa p).2 ⟨hA, h1⟩
      · simp only [Set.mem_singleton_iff] at hn
        rcases hn with rfl
        exact F.inc_QK .a)
  omega

theorem lb_K1 : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inr (.K .one))).ncard := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .one} (a := F.A) (b := F.X .one)
    (F.A_ne_X .one) (F.A_mem_AX .one) (F.X_mem_AX .one)
  have hN : ({p : P | p ∈ F.AX .one}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .one)
  have hT : ({NewPt.Q, .H .one} : Set NewPt).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({p : P | p ∈ F.AX .one} \ {F.A, F.X .one})
    ({NewPt.Q, .H .one} : Set NewPt) (F.lnNb (.inr (.K .one))) (by
      rintro x (⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hA, hn'⟩ := hp
        have h1 : p ≠ F.A := fun e => hn' (by simp [e])
        have h2 : p ≠ F.X .one := fun e => hn' (by simp [e])
        exact (F.inc_pK1 p).2 (Or.inl ⟨hA, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_QK .one
        · exact (F.inc_HK .one .one).2 rfl)
  omega

theorem lb_K2 : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inr (.K .two))).ncard := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .two} (a := F.A) (b := F.X .two)
    (F.A_ne_X .two) (F.A_mem_AX .two) (F.X_mem_AX .two)
  have hN : ({p : P | p ∈ F.AX .two}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .two)
  have hT : ({NewPt.Q, .H .two} : Set NewPt).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({p : P | p ∈ F.AX .two} \ {F.A, F.X .two})
    ({NewPt.Q, .H .two} : Set NewPt) (F.lnNb (.inr (.K .two))) (by
      rintro x (⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hA, hn'⟩ := hp
        have h1 : p ≠ F.A := fun e => hn' (by simp [e])
        have h2 : p ≠ F.X .two := fun e => hn' (by simp [e])
        exact (F.inc_pK2 p).2 (Or.inl ⟨hA, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_QK .two
        · exact (F.inc_HK .two .two).2 rfl)
  omega

theorem lb_K3 : ProjectivePlane.order P L + 1 ≤ (F.lnNb (.inr (.K .three))).ncard := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .three} (a := F.A) (b := F.X .three)
    (F.A_ne_X .three) (F.A_mem_AX .three) (F.X_mem_AX .three)
  have hN : ({p : P | p ∈ F.AX .three}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .three)
  have hT : ({NewPt.Q, .H .three} : Set NewPt).ncard = 2 := Set.ncard_pair (by decide)
  have h := ncard_sum_le ({p : P | p ∈ F.AX .three} \ {F.A, F.X .three})
    ({NewPt.Q, .H .three} : Set NewPt) (F.lnNb (.inr (.K .three))) (by
      rintro x (⟨p, hp, rfl⟩ | ⟨n, hn, rfl⟩)
      · obtain ⟨hA, hn'⟩ := hp
        have h1 : p ≠ F.A := fun e => hn' (by simp [e])
        have h2 : p ≠ F.X .three := fun e => hn' (by simp [e])
        exact (F.inc_pK3 p).2 (Or.inl ⟨hA, h1, h2⟩)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hn
        rcases hn with rfl | rfl
        · exact F.inc_QK .three
        · exact (F.inc_HK .three .three).2 rfl)
  omega

/-- The lower bound for every line of the new structure. -/
theorem lb_ln (x : L ⊕ NewLn) : ProjectivePlane.order P L + 1 ≤ (F.lnNb x).ncard := by
  rcases x with l | n
  · exact F.lb_old_ln l
  · rcases n with _ | h
    · exact F.lb_M
    · rcases h with _ | _ | _ | _
      · exact F.lb_Ka
      · exact F.lb_K1
      · exact F.lb_K2
      · exact F.lb_K3

/-! ### Covered points: plane points on a new line -/

/-- The plane points on the new line `M`. -/
def covM : Set P := {p | p ∈ F.ell} \ {F.X .one, F.X .two, F.X .three}

/-- The plane points on the new line `K a`. -/
def covKa : Set P := {p | p ∈ F.AX .a} \ {F.X .a}

/-- The plane points on the new line `K one`. -/
def covK1 : Set P := ({p | p ∈ F.AX .one} \ {F.A, F.X .one}) ∪ {F.X .three}

/-- The plane points on the new line `K two`. -/
def covK2 : Set P := ({p | p ∈ F.AX .two} \ {F.A, F.X .two}) ∪ {F.X .one}

/-- The plane points on the new line `K three`. -/
def covK3 : Set P := ({p | p ∈ F.AX .three} \ {F.A, F.X .three}) ∪ {F.X .two}

theorem ncard_covM : F.covM.ncard + 3 = ProjectivePlane.order P L + 1 := by
  have hN : ({p : P | p ∈ F.ell}).ncard = ProjectivePlane.order P L + 1 := ncard_points_on F.ell
  have hS := ncard_sub_triple {p : P | p ∈ F.ell} (a := F.X .one) (b := F.X .two)
    (c := F.X .three) (F.X_ne (by decide)) (F.X_ne (by decide)) (F.X_ne (by decide))
    (F.X_mem .one) (F.X_mem .two) (F.X_mem .three)
  unfold covM
  omega

theorem ncard_covKa : F.covKa.ncard + 1 = ProjectivePlane.order P L + 1 := by
  have hS := ncard_diff_one (S := {p : P | p ∈ F.AX .a}) (a := F.X .a) (F.X_mem_AX .a)
  have hN : ({p : P | p ∈ F.AX .a}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .a)
  unfold covKa
  omega

theorem ncard_covK1 : F.covK1.ncard ≤ ProjectivePlane.order P L := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .one} (a := F.A) (b := F.X .one)
    (F.A_ne_X .one) (F.A_mem_AX .one) (F.X_mem_AX .one)
  have hN : ({p : P | p ∈ F.AX .one}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .one)
  have h1 := Set.ncard_union_le ({p : P | p ∈ F.AX .one} \ {F.A, F.X .one}) {F.X .three}
  have h2 := Set.ncard_singleton (F.X .three)
  unfold covK1
  omega

theorem ncard_covK2 : F.covK2.ncard ≤ ProjectivePlane.order P L := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .two} (a := F.A) (b := F.X .two)
    (F.A_ne_X .two) (F.A_mem_AX .two) (F.X_mem_AX .two)
  have hN : ({p : P | p ∈ F.AX .two}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .two)
  have h1 := Set.ncard_union_le ({p : P | p ∈ F.AX .two} \ {F.A, F.X .two}) {F.X .one}
  have h2 := Set.ncard_singleton (F.X .one)
  unfold covK2
  omega

theorem ncard_covK3 : F.covK3.ncard ≤ ProjectivePlane.order P L := by
  have hS := ncard_sub_pair {p : P | p ∈ F.AX .three} (a := F.A) (b := F.X .three)
    (F.A_ne_X .three) (F.A_mem_AX .three) (F.X_mem_AX .three)
  have hN : ({p : P | p ∈ F.AX .three}).ncard = ProjectivePlane.order P L + 1 :=
    ncard_points_on (F.AX .three)
  have h1 := Set.ncard_union_le ({p : P | p ∈ F.AX .three} \ {F.A, F.X .three}) {F.X .two}
  have h2 := Set.ncard_singleton (F.X .two)
  unfold covK3
  omega

/-- The covered points: those on some new line. -/
theorem ncard_cov_le :
    (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3).ncard + 2 ≤ 5 * ProjectivePlane.order P L := by
  have h1 := Set.ncard_union_le (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2) F.covK3
  have h2 := Set.ncard_union_le (F.covM ∪ F.covKa ∪ F.covK1) F.covK2
  have h3 := Set.ncard_union_le (F.covM ∪ F.covKa) F.covK1
  have h4 := Set.ncard_union_le F.covM F.covKa
  have hM := F.ncard_covM
  have hKa := F.ncard_covKa
  have hK1 := F.ncard_covK1
  have hK2 := F.ncard_covK2
  have hK3 := F.ncard_covK3
  omega

/-- A plane point off every covering set lies on no new line, so it has `q + 1` neighbours. -/
theorem ncard_ptNb_old_le (u : P) (hu : u ∉ F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3) :
    (F.ptNb (.inl u)).ncard ≤ ProjectivePlane.order P L + 1 := by
  have hsub : F.ptNb (.inl u) ⊆ Sum.inl '' {l : L | u ∈ l} := by
    intro x hx
    change F.inc (.inl u) x at hx
    rcases x with l | n
    · exact ⟨l, (F.inc_pp u l).1 hx, rfl⟩
    · exfalso
      apply hu
      rcases n with _ | h
      · obtain ⟨hℓ, h1, h2, h3⟩ := (F.inc_pM u).1 hx
        have hM : u ∈ F.covM := Set.mem_sdiff_of_mem hℓ (by simp [h1, h2, h3])
        simp only [Set.mem_union]
        exact Or.inl (Or.inl (Or.inl (Or.inl hM)))
      · rcases h with _ | _ | _ | _
        · obtain ⟨hA, hX⟩ := (F.inc_pKa u).1 hx
          have hK : u ∈ F.covKa := Set.mem_sdiff_of_mem hA (by simp [hX])
          simp only [Set.mem_union]
          exact Or.inl (Or.inl (Or.inl (Or.inr hK)))
        · rcases (F.inc_pK1 u).1 hx with ⟨hA, h1, h2⟩ | h
          · have hK : u ∈ F.covK1 := Set.mem_union_left _ (Set.mem_sdiff_of_mem hA (by simp [h1, h2]))
            simp only [Set.mem_union]
            exact Or.inl (Or.inl (Or.inr hK))
          · have hK : u ∈ F.covK1 := Set.mem_union_right _ (Set.mem_singleton_iff.2 h)
            simp only [Set.mem_union]
            exact Or.inl (Or.inl (Or.inr hK))
        · rcases (F.inc_pK2 u).1 hx with ⟨hA, h1, h2⟩ | h
          · have hK : u ∈ F.covK2 := Set.mem_union_left _ (Set.mem_sdiff_of_mem hA (by simp [h1, h2]))
            simp only [Set.mem_union]
            exact Or.inl (Or.inr hK)
          · have hK : u ∈ F.covK2 := Set.mem_union_right _ (Set.mem_singleton_iff.2 h)
            simp only [Set.mem_union]
            exact Or.inl (Or.inr hK)
        · rcases (F.inc_pK3 u).1 hx with ⟨hA, h1, h2⟩ | h
          · have hK : u ∈ F.covK3 := Set.mem_union_left _ (Set.mem_sdiff_of_mem hA (by simp [h1, h2]))
            simp only [Set.mem_union]
            exact Or.inr hK
          · have hK : u ∈ F.covK3 := Set.mem_union_right _ (Set.mem_singleton_iff.2 h)
            simp only [Set.mem_union]
            exact Or.inr hK
  have h := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_image_of_injective _ Sum.inl_injective, ncard_lines_through] at h
  exact h

/-- The deficit of the plane points is at least the number of uncovered plane points. -/
theorem sum_deficit_ge [Fintype P] [Fintype L] :
    (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3)ᶜ.ncard ≤
      ∑ a : P ⊕ NewPt, (ProjectivePlane.order P L + 2 - BipartiteDD.Regular.degL F.inc a) := by
  rw [Fintype.sum_sum_type]
  have h1 : (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3)ᶜ.ncard ≤
      ∑ u : P, (ProjectivePlane.order P L + 2 - BipartiteDD.Regular.degL F.inc (.inl u)) := by
    apply sum_ge_ncard
    intro u hu
    have hle := F.ncard_ptNb_old_le u hu
    have hd : BipartiteDD.Regular.degL F.inc (.inl u) = (F.ptNb (.inl u)).ncard := rfl
    rw [hd]
    omega
  exact le_trans h1 (Nat.le_add_right _ _)

/-! ### The hypotheses of the completion lemma -/

theorem degL_le (a : P ⊕ NewPt) : BipartiteDD.Regular.degL F.inc a ≤ ProjectivePlane.order P L + 2 :=
  F.point_degree a

theorem deficit_le (a : P ⊕ NewPt) :
    ProjectivePlane.order P L + 2 - BipartiteDD.Regular.degL F.inc a ≤ 1 := by
  have h := F.lb_pt a
  have hd : BipartiteDD.Regular.degL F.inc a = (F.ptNb a).ncard := rfl
  rw [hd]
  omega

theorem degR_le (b : L ⊕ NewLn) : BipartiteDD.Regular.degR F.inc b ≤ ProjectivePlane.order P L + 2 :=
  F.line_degree b

theorem deficit_le_ln (b : L ⊕ NewLn) :
    ProjectivePlane.order P L + 2 - BipartiteDD.Regular.degR F.inc b ≤ 1 := by
  have h := F.lb_ln b
  have hd : BipartiteDD.Regular.degR F.inc b = (F.lnNb b).ncard := rfl
  rw [hd]
  omega

theorem card_eq_sides [Fintype P] [Fintype L] : Fintype.card (P ⊕ NewPt) = Fintype.card (L ⊕ NewLn) := by
  have h5 : Fintype.card NewPt = 5 := rfl
  have h5' : Fintype.card NewLn = 5 := rfl
  rw [Fintype.card_sum, Fintype.card_sum, h5, h5', ProjectivePlane.card_points P L,
    ProjectivePlane.card_lines P L]

/-- The total deficit is large enough for the completion lemma when `q ≥ 7`. -/
theorem hbig [Fintype P] [Fintype L] (hq : 7 ≤ ProjectivePlane.order P L) :
    2 * 1 * (ProjectivePlane.order P L + 2 + 1 + 1) <
      ∑ a : P ⊕ NewPt, (ProjectivePlane.order P L + 2 - BipartiteDD.Regular.degL F.inc a) := by
  have hcov := F.ncard_cov_le
  have hsum := F.sum_deficit_ge
  have hcompl := Set.ncard_add_ncard_compl (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3)
  have hP : Nat.card P = ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 1 := by
    rw [Nat.card_eq_fintype_card, ProjectivePlane.card_points P L]
  rw [hP] at hcompl
  have hq2 : 7 * ProjectivePlane.order P L ≤ ProjectivePlane.order P L ^ 2 := by nlinarith
  have key : 2 * ProjectivePlane.order P L + 8 <
      (F.covM ∪ F.covKa ∪ F.covK1 ∪ F.covK2 ∪ F.covK3)ᶜ.ncard := by
    omega
  have e : 2 * 1 * (ProjectivePlane.order P L + 2 + 1 + 1) = 2 * ProjectivePlane.order P L + 8 := by
    ring
  rw [e]
  exact lt_of_lt_of_le key hsum

end Frame

/-- The regular `+2` theorem: for every finite projective plane of order `q ≥ 7`, there is a
`(q + 2)`-regular bipartite graph on `2 (q² + q + 6)` vertices with diameter at most `3`. -/
theorem zero_isBipartiteRegDiam {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Fintype L] (h : 7 ≤ ProjectivePlane.order P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      BipartiteDD.IsBipartiteRegDiam G (ProjectivePlane.order P L + 2) 3 := by
  obtain ⟨F⟩ := Frame.exists (show 3 ≤ ProjectivePlane.order P L by omega)
  have hdiam : (BipartiteDD.Regular.biGraph F.inc).ediam ≤ 3 := by
    rw [← F.graph_eq_biGraph]
    exact F.ediam_le
  obtain ⟨G, hG⟩ := BipartiteDD.Regular.exists_regular_completion_fin F.inc
    (ProjectivePlane.order P L + 2) 1 3 F.degL_le F.degR_le F.deficit_le F.deficit_le_ln
    Frame.card_eq_sides (F.hbig h) hdiam
  have hn : 2 * Fintype.card (P ⊕ NewPt) =
      2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6) := by
    rw [Fintype.card_sum, show Fintype.card NewPt = 5 from rfl, ProjectivePlane.card_points P L]
  exact ⟨G.comap (finCongr hn).symm, hG.comap (finCongr hn)⟩

end BipartiteDD.Plus2Zero
