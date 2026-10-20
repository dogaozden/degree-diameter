import BipartiteDD.Plus2.Exists
import BipartiteDD.Regular.Completion

/-! Regularity, part 2a: geometry of the deficient vertices of the `+2` graph.

For a frame `F` of a finite projective plane of order `q`, the points of the plane that are off `ℓ`, not `A`,
and on no line `AX s` are the *deficient points* `defPt`; the lines that are not `ℓ`, avoid `A`, and avoid
every `X s` are the *deficient lines* `defLn`. They are exactly the vertices of degree `q + 1` of the `+2`
graph (REPORT / coords.tex, Table 1). This file counts them (`(q-1)(q-3)` of each) and shows that a deficient
point is on at most `q - 4` deficient lines and a deficient line carries at most `q - 4` deficient points. -/

namespace BipartiteDD.Plus2.Frame

open Configuration Finset
open scoped Classical
open BipartiteDD.Regular

variable {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
variable (F : Frame P L)

/-- A point of the plane off `ℓ`, different from `A`, and on no line `AX s`. -/
def defPt (p : P) : Prop := p ∉ F.ell ∧ p ≠ F.A ∧ ∀ s, p ∉ F.AX s

/-- A line of the plane different from `ℓ`, not through `A`, and through no `X s`. -/
def defLn (l : L) : Prop := l ≠ F.ell ∧ F.A ∉ l ∧ ∀ s, F.X s ∉ l

theorem card_pts_on (l : L) : (univ.filter fun p : P => p ∈ l).card = ProjectivePlane.order P L + 1 := by
  rw [← ncard_setOf_eq_card_filter]
  exact ncard_points_on l

theorem card_lns_through (p : P) :
    (univ.filter fun l : L => p ∈ l).card = ProjectivePlane.order P L + 1 := by
  rw [← ncard_setOf_eq_card_filter]
  exact ncard_lines_through p

theorem Row.univ_eq : (Finset.univ : Finset Row) = {.r0, .r1, .ra, .rc} := rfl

/-- At most one line `AX s` passes through a point other than `A`. -/
theorem AX_unique {p : P} (hp : p ≠ F.A) {s t : Row} (hs : p ∈ F.AX s) (ht : p ∈ F.AX t) : s = t := by
  by_contra hst
  exact hp (F.eq_A_of_mem_AX_AX hst hs ht)

/-- A point of `AX s` off `ℓ` and different from `A`. -/
noncomputable def offPts (s : Row) : Finset P := univ.filter fun p => p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A

theorem card_offPts (s : Row) : (F.offPts s).card + 2 = ProjectivePlane.order P L + 1 := by
  have hsub : F.offPts s ∪ {F.A, F.X s} = univ.filter fun p : P => p ∈ F.AX s := by
    ext p
    simp only [offPts, mem_union, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · rw [h]; exact F.A_mem_AX s
      · rw [h]; exact F.X_mem_AX s
    · intro h
      by_cases hA : p = F.A
      · exact Or.inr (Or.inl hA)
      by_cases hE : p ∈ F.ell
      · exact Or.inr (Or.inr ((F.mem_AX_iff s hE).1 h))
      · exact Or.inl ⟨h, hE, hA⟩
  have hdisj : Disjoint (F.offPts s) {F.A, F.X s} := by
    rw [disjoint_left]
    intro p hp hp'
    simp only [offPts, mem_filter, mem_univ, true_and] at hp
    simp only [mem_insert, mem_singleton] at hp'
    rcases hp' with h | h
    · exact hp.2.2 h
    · exact hp.2.1 (h ▸ F.X_mem s)
  have h2 : ({F.A, F.X s} : Finset P).card = 2 := card_pair (F.A_ne_X s)
  have := card_union_of_disjoint hdisj
  rw [hsub, h2, card_pts_on] at this
  omega

/-- The partition of the points of the plane into deficient points, points of `ℓ`, `A`, and the sets `offPts s`. -/
theorem pt_partition (p : P) :
    (if F.defPt p then 1 else 0) + (if p ∈ F.ell then 1 else 0) + (if p = F.A then 1 else 0) +
      ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) = 1 := by
  by_cases hE : p ∈ F.ell
  · have hA : p ≠ F.A := fun h => F.A_not_mem (h ▸ hE)
    have h1 : ¬ F.defPt p := fun h => h.1 hE
    have h2 : ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => h.2.1 hE)
    rw [if_neg h1, if_pos hE, if_neg hA, h2]
  by_cases hA : p = F.A
  · have h1 : ¬ F.defPt p := fun h => h.2.1 hA
    have h2 : ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => h.2.2 hA)
    rw [if_neg h1, if_neg hE, if_pos hA, h2]
  by_cases hex : ∃ s, p ∈ F.AX s
  · obtain ⟨s0, hs0⟩ := hex
    have h1 : ¬ F.defPt p := fun h => h.2.2 s0 hs0
    have h2 : ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) = 1 := by
      rw [sum_eq_single s0]
      · exact if_pos ⟨hs0, hE, hA⟩
      · intro t _ ht
        exact if_neg (fun h => ht (F.AX_unique hA h.1 hs0))
      · intro h
        exact absurd (mem_univ s0) h
    rw [if_neg h1, if_neg hE, if_neg hA, h2]
  · push Not at hex
    have h1 : F.defPt p := ⟨hE, hA, hex⟩
    have h2 : ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => hex s h.1)
    rw [if_pos h1, if_neg hE, if_neg hA, h2]

/-- The number of deficient points: `|defPt| + 4 q = q² + 3`, i.e. `(q-1)(q-3)`. -/
theorem card_defPt : (univ.filter F.defPt).card + 4 * ProjectivePlane.order P L =
    ProjectivePlane.order P L ^ 2 + 3 := by
  have h : ∑ p : P, ((if F.defPt p then 1 else 0) + (if p ∈ F.ell then 1 else 0) +
      (if p = F.A then 1 else 0) +
      ∑ s, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0)) = ∑ _p : P, 1 :=
    sum_congr rfl fun p _ => F.pt_partition p
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib] at h
  have hPs : ∑ p : P, (if F.defPt p then 1 else 0) = (univ.filter F.defPt).card :=
    (card_filter _ _).symm
  have hE1 : ∑ p : P, (if p ∈ F.ell then 1 else 0) = ProjectivePlane.order P L + 1 := by
    rw [← card_filter]
    exact card_pts_on F.ell
  have hA1 : ∑ p : P, (if p = F.A then 1 else 0) = 1 := by simp
  have hB : ∑ p : P, ∑ s : Row, (if p ∈ F.AX s ∧ p ∉ F.ell ∧ p ≠ F.A then 1 else 0) =
      ∑ s : Row, (F.offPts s).card := by
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [offPts, card_filter]
  rw [hPs, hE1, hA1, hB] at h
  have h3 : ∑ s : Row, (F.offPts s).card + ∑ _s : Row, 2 =
      ∑ _s : Row, (ProjectivePlane.order P L + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun s _ => F.card_offPts s
  have h4 : Fintype.card Row = 4 := rfl
  simp only [sum_const, card_univ, smul_eq_mul, h4] at h3 h
  have h6 := ProjectivePlane.card_points P L
  rw [Fintype.card_eq_nat_card] at h
  rw [Fintype.card_eq_nat_card] at h6
  have : ProjectivePlane.order P L ^ 2 = ProjectivePlane.order P L * ProjectivePlane.order P L := sq _
  nlinarith

/-- At most one point `X s` lies on a line other than `ℓ`. -/
theorem X_unique {l : L} (hl : l ≠ F.ell) {s t : Row} (hs : F.X s ∈ l) (ht : F.X t ∈ l) : s = t := by
  by_contra hst
  rcases Nondegenerate.eq_or_eq (F.X_mem s) (F.X_mem t) hs ht with e | e
  · exact hst (F.X_inj e)
  · exact hl e.symm

/-- A line through `X s`, not `ℓ`, not through `A`. -/
noncomputable def offLns (s : Row) : Finset L :=
  univ.filter fun l => F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l

theorem card_offLns (s : Row) : (F.offLns s).card + 2 = ProjectivePlane.order P L + 1 := by
  have hsub : F.offLns s ∪ {F.ell, F.AX s} = univ.filter fun l : L => F.X s ∈ l := by
    ext l
    simp only [offLns, mem_union, mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · rintro (⟨h, -⟩ | h | h)
      · exact h
      · rw [h]; exact F.X_mem s
      · rw [h]; exact F.X_mem_AX s
    · intro h
      by_cases hE : l = F.ell
      · exact Or.inr (Or.inl hE)
      by_cases hA : F.A ∈ l
      · exact Or.inr (Or.inr (F.eq_AX_of_mem s hA h))
      · exact Or.inl ⟨h, hE, hA⟩
  have hdisj : Disjoint (F.offLns s) {F.ell, F.AX s} := by
    rw [disjoint_left]
    intro l hl hl'
    simp only [offLns, mem_filter, mem_univ, true_and] at hl
    simp only [mem_insert, mem_singleton] at hl'
    rcases hl' with h | h
    · exact hl.2.1 h
    · exact hl.2.2 (h ▸ F.A_mem_AX s)
  have h2 : ({F.ell, F.AX s} : Finset L).card = 2 := card_pair (F.AX_ne_ell s).symm
  have := card_union_of_disjoint hdisj
  rw [hsub, h2, card_lns_through] at this
  omega

/-- The partition of the lines of the plane into deficient lines, lines through `A`, `ℓ`, and the sets
`offLns s`. -/
theorem ln_partition (l : L) :
    (if F.defLn l then 1 else 0) + (if F.A ∈ l then 1 else 0) + (if l = F.ell then 1 else 0) +
      ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) = 1 := by
  by_cases hA : F.A ∈ l
  · have hE : l ≠ F.ell := fun h => F.A_not_mem (h ▸ hA)
    have h1 : ¬ F.defLn l := fun h => h.2.1 hA
    have h2 : ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => h.2.2 hA)
    rw [if_neg h1, if_pos hA, if_neg hE, h2]
  by_cases hE : l = F.ell
  · have h1 : ¬ F.defLn l := fun h => h.1 hE
    have h2 : ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => h.2.1 hE)
    rw [if_neg h1, if_neg hA, if_pos hE, h2]
  by_cases hex : ∃ s, F.X s ∈ l
  · obtain ⟨s0, hs0⟩ := hex
    have h1 : ¬ F.defLn l := fun h => h.2.2 s0 hs0
    have h2 : ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) = 1 := by
      rw [sum_eq_single s0]
      · exact if_pos ⟨hs0, hE, hA⟩
      · intro t _ ht
        exact if_neg (fun h => ht (F.X_unique hE h.1 hs0))
      · intro h
        exact absurd (mem_univ s0) h
    rw [if_neg h1, if_neg hA, if_neg hE, h2]
  · push Not at hex
    have h1 : F.defLn l := ⟨hE, hA, hex⟩
    have h2 : ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) = 0 :=
      sum_eq_zero fun s _ => if_neg (fun h => hex s h.1)
    rw [if_pos h1, if_neg hA, if_neg hE, h2]

/-- The number of deficient lines: `|defLn| + 4 q = q² + 3`, i.e. `(q-1)(q-3)`. -/
theorem card_defLn : (univ.filter F.defLn).card + 4 * ProjectivePlane.order P L =
    ProjectivePlane.order P L ^ 2 + 3 := by
  have h : ∑ l : L, ((if F.defLn l then 1 else 0) + (if F.A ∈ l then 1 else 0) +
      (if l = F.ell then 1 else 0) +
      ∑ s, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0)) = ∑ _l : L, 1 :=
    sum_congr rfl fun l _ => F.ln_partition l
  rw [sum_add_distrib, sum_add_distrib, sum_add_distrib] at h
  have hLs : ∑ l : L, (if F.defLn l then 1 else 0) = (univ.filter F.defLn).card :=
    (card_filter _ _).symm
  have hA1 : ∑ l : L, (if F.A ∈ l then 1 else 0) = ProjectivePlane.order P L + 1 := by
    rw [← card_filter]
    exact card_lns_through F.A
  have hE1 : ∑ l : L, (if l = F.ell then 1 else 0) = 1 := by simp
  have hB : ∑ l : L, ∑ s : Row, (if F.X s ∈ l ∧ l ≠ F.ell ∧ F.A ∉ l then 1 else 0) =
      ∑ s : Row, (F.offLns s).card := by
    rw [sum_comm]
    refine sum_congr rfl fun s _ => ?_
    rw [offLns, card_filter]
  rw [hLs, hA1, hE1, hB] at h
  have h3 : ∑ s : Row, (F.offLns s).card + ∑ _s : Row, 2 =
      ∑ _s : Row, (ProjectivePlane.order P L + 1) := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun s _ => F.card_offLns s
  have h4 : Fintype.card Row = 4 := rfl
  simp only [sum_const, card_univ, smul_eq_mul, h4] at h3 h
  have h6 := ProjectivePlane.card_lines P L
  rw [Fintype.card_eq_nat_card] at h
  rw [Fintype.card_eq_nat_card] at h6
  have : ProjectivePlane.order P L ^ 2 = ProjectivePlane.order P L * ProjectivePlane.order P L := sq _
  nlinarith

/-- Five distinct elements of `T` outside `S ⊆ T`. -/
theorem card_add_five_le {X : Type*} [Fintype X] (S T : Finset X) (hsub : S ⊆ T) (f : Option Row → X)
    (hf : Function.Injective f) (hT : ∀ i, f i ∈ T) (hS : ∀ i, f i ∉ S) : S.card + 5 ≤ T.card := by
  have hI : (univ.image f).card = 5 := by
    rw [card_image_of_injective _ hf, card_univ, Fintype.card_option]
    rfl
  have hd : Disjoint S (univ.image f) := by
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := mem_image.1 hx'
    exact hS i hx
  have hu : S ∪ univ.image f ⊆ T := by
    intro x hx
    rcases mem_union.1 hx with h | h
    · exact hsub h
    · obtain ⟨i, -, rfl⟩ := mem_image.1 h
      exact hT i
  have := card_le_card hu
  rw [card_union_of_disjoint hd, hI] at this
  exact this

/-- The five lines through a deficient point `p` that are not deficient: the line `pA` and the four lines
`pX s`. -/
noncomputable def fiveLines (p : P) (hA : p ≠ F.A) (hE : p ∉ F.ell) : Option Row → L
  | none => HasLines.mkLine hA
  | some s => HasLines.mkLine (show p ≠ F.X s from fun h => hE (h ▸ F.X_mem s))

/-- A deficient point lies on at most `q - 4` deficient lines. -/
theorem card_defLn_through {p : P} (hp : F.defPt p) :
    (univ.filter fun l : L => p ∈ l ∧ F.defLn l).card + 5 ≤ ProjectivePlane.order P L + 1 := by
  obtain ⟨hE, hA, hX⟩ := hp
  have hpX : ∀ s, p ≠ F.X s := fun s h => hE (h ▸ F.X_mem s)
  have hmem : ∀ i, p ∈ F.fiveLines p hA hE i := by
    intro i
    rcases i with _ | s
    · exact (HasLines.mkLine_ax hA).1
    · exact (HasLines.mkLine_ax (hpX s)).1
  rw [← card_lns_through p]
  refine card_add_five_le _ _ (fun l hl => by simp only [mem_filter, mem_univ, true_and] at hl ⊢; exact hl.1)
    (F.fiveLines p hA hE) ?_ (fun i => by simpa using hmem i) ?_
  · intro i j hij
    rcases i with _ | s <;> rcases j with _ | t
    · rfl
    · exfalso
      have h1 : F.A ∈ F.fiveLines p hA hE (some t) := hij ▸ (HasLines.mkLine_ax hA).2
      have h2 : F.X t ∈ F.fiveLines p hA hE (some t) := (HasLines.mkLine_ax (hpX t)).2
      exact hX t (F.eq_AX_of_mem t h1 h2 ▸ hmem (some t))
    · exfalso
      have h1 : F.A ∈ F.fiveLines p hA hE (some s) := hij ▸ (HasLines.mkLine_ax hA).2
      have h2 : F.X s ∈ F.fiveLines p hA hE (some s) := (HasLines.mkLine_ax (hpX s)).2
      exact hX s (F.eq_AX_of_mem s h1 h2 ▸ hmem (some s))
    · have h1 : F.X s ∈ F.fiveLines p hA hE (some s) := (HasLines.mkLine_ax (hpX s)).2
      have h2 : F.X t ∈ F.fiveLines p hA hE (some s) := hij ▸ (HasLines.mkLine_ax (hpX t)).2
      have hne : F.fiveLines p hA hE (some s) ≠ F.ell := fun h => hE (h ▸ hmem (some s))
      exact congrArg some (F.X_unique hne h1 h2)
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rcases i with _ | s
    · exact hi.2.2.1 (HasLines.mkLine_ax hA).2
    · exact hi.2.2.2 s (HasLines.mkLine_ax (hpX s)).2

/-- The five points of a deficient line `l` that are not deficient: `l ∩ ℓ` and the four points `l ∩ AX s`. -/
noncomputable def fivePoints (l : L) (hE : l ≠ F.ell) (hA : F.A ∉ l) : Option Row → P
  | none => HasPoints.mkPoint hE
  | some s => HasPoints.mkPoint (show l ≠ F.AX s from fun h => hA (h ▸ F.A_mem_AX s))

/-- A deficient line carries at most `q - 4` deficient points. -/
theorem card_defPt_on {l : L} (hl : F.defLn l) :
    (univ.filter fun p : P => p ∈ l ∧ F.defPt p).card + 5 ≤ ProjectivePlane.order P L + 1 := by
  obtain ⟨hE, hA, hX⟩ := hl
  have hlAX : ∀ s, l ≠ F.AX s := fun s h => hA (h ▸ F.A_mem_AX s)
  have hmem : ∀ i, F.fivePoints l hE hA i ∈ l := by
    intro i
    rcases i with _ | s
    · exact (HasPoints.mkPoint_ax hE).1
    · exact (HasPoints.mkPoint_ax (hlAX s)).1
  rw [← card_pts_on l]
  refine card_add_five_le _ _ (fun p hp => by simp only [mem_filter, mem_univ, true_and] at hp ⊢; exact hp.1)
    (F.fivePoints l hE hA) ?_ (fun i => by simpa using hmem i) ?_
  · intro i j hij
    rcases i with _ | s <;> rcases j with _ | t
    · rfl
    · exfalso
      have h1 : F.fivePoints l hE hA none ∈ F.ell := (HasPoints.mkPoint_ax hE).2
      have h2 : F.fivePoints l hE hA none ∈ F.AX t := hij ▸ (HasPoints.mkPoint_ax (hlAX t)).2
      exact hX t ((F.mem_AX_iff t h1).1 h2 ▸ hmem none)
    · exfalso
      have h1 : F.fivePoints l hE hA none ∈ F.ell := (HasPoints.mkPoint_ax hE).2
      have h2 : F.fivePoints l hE hA none ∈ F.AX s := hij ▸ (HasPoints.mkPoint_ax (hlAX s)).2
      exact hX s ((F.mem_AX_iff s h1).1 h2 ▸ hmem none)
    · by_contra hst
      have hst' : s ≠ t := fun e => hst (congrArg some e)
      have h1 : F.fivePoints l hE hA (some s) ∈ F.AX s := (HasPoints.mkPoint_ax (hlAX s)).2
      have h2 : F.fivePoints l hE hA (some s) ∈ F.AX t := hij ▸ (HasPoints.mkPoint_ax (hlAX t)).2
      exact hA (F.eq_A_of_mem_AX_AX hst' h1 h2 ▸ hmem (some s))
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rcases i with _ | s
    · exact hi.2.1 (HasPoints.mkPoint_ax hE).2
    · exact hi.2.2.2 s (HasPoints.mkPoint_ax (hlAX s)).2

end BipartiteDD.Plus2.Frame
