import BipartiteDD.LeanMaxx.D5.Reach
import BipartiteDD.GQST.Diam

/-! # D = 5 formalisation, part 2: the base facts of a generalized quadrangle

Facts F1–F3 of `research/theorems/D5_QUADRANGLE.md` §1.1 in the form used by the level-graph theorems, for the
incidence graph `I = incGraph P L` of a generalized quadrangle `GQst P L s t` with `s, t ≥ 1`:

* `Base.all4`: any two elements are within `4`; `Base.odd3`: two elements of different colour within `3`;
* `Base.two`: every element has two different neighbours;
* `Base.cover`: (F3) for elements `x, y` of different colour there is `z`, at distance `2` from `x`
  (`Co x z`), adjacent to `y`.

`col` is `false` on points and `true` on lines; `Co x y` says that `x ≠ y` have a common neighbour (distance two). -/

namespace BipartiteDD.LeanMaxx.D5

open SimpleGraph BipartiteDD

variable {P L : Type*} [Membership P L]

/-- The colour of an element of `P ⊕ L`: `false` for points, `true` for lines. -/
def col : P ⊕ L → Bool
  | .inl _ => false
  | .inr _ => true

/-- Two different elements with a common neighbour (`x ∈ Γ₂(y)`). -/
def Co (x y : P ⊕ L) : Prop :=
  x ≠ y ∧ ∃ z, (incGraph P L).Adj x z ∧ (incGraph P L).Adj z y

theorem col_adj {x y : P ⊕ L} (h : (incGraph P L).Adj x y) : col x ≠ col y := by
  rcases x with p | l <;> rcases y with p' | l'
  · exact absurd h incGraph_not_adj_inl_inl
  · simp [col]
  · simp [col]
  · exact absurd h incGraph_not_adj_inr_inr

theorem col_adj_not {x y : P ⊕ L} (h : (incGraph P L).Adj x y) : col x = !col y := by
  have := col_adj h
  cases hx : col x <;> cases hy : col y <;> simp_all

theorem Co.col_eq {x y : P ⊕ L} (h : Co x y) : col x = col y := by
  obtain ⟨-, z, h1, h2⟩ := h
  have := col_adj_not h1; have := col_adj_not h2
  cases hx : col x <;> cases hz : col z <;> cases hy : col y <;> simp_all

theorem Co.symm {x y : P ⊕ L} (h : Co x y) : Co y x := by
  obtain ⟨hne, z, h1, h2⟩ := h
  exact ⟨hne.symm, z, h2.symm, h1.symm⟩

theorem Co.reach {x y : P ⊕ L} (h : Co x y) : Reach (incGraph P L) x y 2 := by
  obtain ⟨-, z, h1, h2⟩ := h
  exact Reach.two h1 h2

/-- Parity: the length of a walk is even iff its ends have the same colour. -/
theorem walk_parity {x y : P ⊕ L} (w : (incGraph P L).Walk x y) :
    (w.length % 2 = 0 ↔ col x = col y) := by
  induction w with
  | nil => simp
  | @cons u v z h w ih =>
    have e := col_adj_not h
    rw [Walk.length_cons, e]
    cases hv : col v <;> cases hz : col z <;> simp_all <;> omega

/-- A walk of length at most `2` between different elements of the same colour: they are `Co`. -/
theorem Reach.co_of_two {x y : P ⊕ L} (hne : x ≠ y) (hc : col x = col y)
    (h : Reach (incGraph P L) x y 2) : Co x y := by
  obtain ⟨w, hw⟩ := h
  have hpar := (walk_parity w).2 hc
  cases w with
  | nil => exact absurd rfl hne
  | cons h1 w' =>
    cases w' with
    | nil => simp at hpar
    | cons h2 w'' =>
      cases w'' with
      | nil => exact ⟨hne, _, h1, h2⟩
      | cons h3 w3 => simp at hw

/-- Two different elements of different colour joined by a walk of length at most `1` are adjacent. -/
theorem Reach.adj_of_one {x y : P ⊕ L} (hc : col x ≠ col y) (h : Reach (incGraph P L) x y 1) :
    (incGraph P L).Adj x y := by
  obtain ⟨w, hw⟩ := h
  cases w with
  | nil => exact absurd rfl hc
  | cons h1 w' =>
    cases w' with
    | nil => exact h1
    | cons h2 w'' => simp at hw

/-- The base facts used by the level-graph theorems. -/
structure Base (P L : Type*) [Membership P L] : Prop where
  all4 : ∀ x y : P ⊕ L, Reach (incGraph P L) x y 4
  odd3 : ∀ x y : P ⊕ L, col x ≠ col y → Reach (incGraph P L) x y 3
  two : ∀ x : P ⊕ L, ∃ y y', y ≠ y' ∧ (incGraph P L).Adj x y ∧ (incGraph P L).Adj x y'
  cover : ∀ x y : P ⊕ L, col x ≠ col y → ∃ z, Co x z ∧ (incGraph P L).Adj z y

end BipartiteDD.LeanMaxx.D5

namespace BipartiteDD.GQst

open SimpleGraph BipartiteDD.LeanMaxx.D5

variable {P L : Type*} [Membership P L] {s t : ℕ}

/-- A point and a line are within `3`. -/
theorem reach_pt_line (G : GQst P L s t) (p : P) (l : L) :
    Reach (incGraph P L) (.inl p) (.inr l) 3 := by
  by_cases h : p ∈ l
  · exact (Reach.adj (incGraph_adj_inl_inr.2 h)).mono (by norm_num)
  · obtain ⟨x, hxl, m, hpm, hxm⟩ := G.gq_ax p l h
    exact (Reach.two (incGraph_adj_inl_inr.2 hpm) (incGraph_adj_inr_inl.2 hxm)).trans
      (Reach.adj (incGraph_adj_inl_inr.2 hxl))

theorem two_pts (G : GQst P L (s + 1) t) (l : L) : ∃ p p' : P, p ≠ p' ∧ p ∈ l ∧ p' ∈ l := by
  have h : 1 < Nat.card {p : P // p ∈ l} := by rw [G.pts_on_line l]; omega
  have : Finite {p : P // p ∈ l} := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial {p : P // p ∈ l} := Finite.one_lt_card_iff_nontrivial.mp h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne {p : P // p ∈ l}
  exact ⟨a, b, fun h => hab (Subtype.ext h), ha, hb⟩

theorem two_lines (G : GQst P L s (t + 1)) (p : P) : ∃ l l' : L, l ≠ l' ∧ p ∈ l ∧ p ∈ l' := by
  have h : 1 < Nat.card {l : L // p ∈ l} := by rw [G.lines_on_pt p]; omega
  have : Finite {l : L // p ∈ l} := Nat.finite_of_card_ne_zero (by omega)
  have : Nontrivial {l : L // p ∈ l} := Finite.one_lt_card_iff_nontrivial.mp h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hab⟩ := exists_pair_ne {l : L // p ∈ l}
  exact ⟨a, b, fun h => hab (Subtype.ext h), ha, hb⟩

/-- The base facts follow from the axioms (for `s, t ≥ 1`). -/
theorem base (G : GQst P L (s + 1) (t + 1)) : Base P L where
  all4 := by
    rintro (p | l) (r | m)
    · obtain ⟨l, hl⟩ := G.exists_line r
      exact ((G.reach_pt_line p l).trans (Reach.adj (incGraph_adj_inr_inl.2 hl))).mono (by norm_num)
    · exact (G.reach_pt_line p m).mono (by norm_num)
    · exact (G.reach_pt_line r l).symm.mono (by norm_num)
    · obtain ⟨p, hp⟩ := G.exists_pt l
      exact ((Reach.adj (incGraph_adj_inr_inl.2 hp)).trans (G.reach_pt_line p m)).mono (by norm_num)
  odd3 := by
    rintro (p | l) (r | m) h
    · simp [col] at h
    · exact G.reach_pt_line p m
    · exact (G.reach_pt_line r l).symm
    · simp [col] at h
  two := by
    rintro (p | l)
    · obtain ⟨l, l', hne, hl, hl'⟩ := G.two_lines p
      exact ⟨.inr l, .inr l', by simpa using hne, incGraph_adj_inl_inr.2 hl, incGraph_adj_inl_inr.2 hl'⟩
    · obtain ⟨p, p', hne, hp, hp'⟩ := G.two_pts l
      exact ⟨.inl p, .inl p', by simpa using hne, incGraph_adj_inr_inl.2 hp, incGraph_adj_inr_inl.2 hp'⟩
  cover := by
    rintro (p | l) (r | m) h
    · simp [col] at h
    · -- point `p`, line `m`
      by_cases hpm : p ∈ m
      · obtain ⟨p', p'', hne, h1, h2⟩ := G.two_pts m
        have : ∃ z : P, z ∈ m ∧ z ≠ p := by
          by_cases e : p' = p
          · exact ⟨p'', h2, fun h => hne (e.trans h.symm)⟩
          · exact ⟨p', h1, e⟩
        obtain ⟨z, hz, hzp⟩ := this
        exact ⟨.inl z, ⟨fun h => hzp (Sum.inl_injective h).symm, .inr m, incGraph_adj_inl_inr.2 hpm,
          incGraph_adj_inr_inl.2 hz⟩, incGraph_adj_inl_inr.2 hz⟩
      · obtain ⟨x, hxm, l, hpl, hxl⟩ := G.gq_ax p m hpm
        have hxp : x ≠ p := fun h => hpm (h ▸ hxm)
        exact ⟨.inl x, ⟨fun h => hxp (Sum.inl_injective h).symm, .inr l, incGraph_adj_inl_inr.2 hpl,
          incGraph_adj_inr_inl.2 hxl⟩, incGraph_adj_inl_inr.2 hxm⟩
    · -- line `l`, point `r`
      by_cases hrl : r ∈ l
      · obtain ⟨l', l'', hne, h1, h2⟩ := G.two_lines r
        have : ∃ z : L, r ∈ z ∧ z ≠ l := by
          by_cases e : l' = l
          · exact ⟨l'', h2, fun h => hne (e.trans h.symm)⟩
          · exact ⟨l', h1, e⟩
        obtain ⟨z, hz, hzl⟩ := this
        exact ⟨.inr z, ⟨fun h => hzl (Sum.inr_injective h).symm, .inl r, incGraph_adj_inr_inl.2 hrl,
          incGraph_adj_inl_inr.2 hz⟩, incGraph_adj_inr_inl.2 hz⟩
      · obtain ⟨x, hxl, m, hrm, hxm⟩ := G.gq_ax r l hrl
        have hml : m ≠ l := fun h => hrl (h ▸ hrm)
        exact ⟨.inr m, ⟨fun h => hml (Sum.inr_injective h).symm, .inl x, incGraph_adj_inr_inl.2 hxl,
          incGraph_adj_inl_inr.2 hxm⟩, incGraph_adj_inr_inl.2 hrm⟩
    · simp [col] at h

end BipartiteDD.GQst
