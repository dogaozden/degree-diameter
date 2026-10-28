import BipartiteDD.HexagonD7.Defs

/-! Diameter 7 from a generalized hexagon, part 2: the covering lemma.

If every point is on two lines, then for a line `ℓ` and a point `x` joined by a walk of length at most `5`,
some line `ℓ'` concurrent with `ℓ` (and different from it) is joined to `x` by a walk of length at most `3`.
Dually for a point `p` and a line `m`. No girth is used: a walk that comes back to `ℓ` after two steps is
shortened. -/

namespace BipartiteDD.HexagonD7

open SimpleGraph BipartiteDD.Hexagon

variable {P L : Type*} {inc : P → L → Prop}

theorem cover_aux (hP2 : ∀ p, ∃ l l', l ≠ l' ∧ inc p l ∧ inc p l') (x : P) :
    ∀ n, n ≤ 5 → ∀ (ℓ : L) (w : (Hexagon.incGraph inc).Walk (.inr ℓ) (.inl x)), w.length ≤ n →
      ∃ ℓ', Conc inc ℓ ℓ' ∧ Reach (Hexagon.incGraph inc) (.inr ℓ') (.inl x) 3 := by
  intro n
  induction n with
  | zero =>
    intro _ ℓ w hw
    cases w with
    | cons h w' => simp at hw
  | succ n ih =>
    intro hn ℓ w hw
    cases w with
    | cons h1 w1 =>
      rename_i b
      cases b with
      | inr l => exact absurd h1 Hexagon.incGraph_not_adj_inr_inr
      | inl y =>
        have h1' : inc y ℓ := Hexagon.incGraph_adj_inr_inl.1 h1
        cases w1 with
        | nil =>
          obtain ⟨l, l', hll', hl, hl'⟩ := hP2 x
          by_cases hlℓ : l = ℓ
          · subst hlℓ
            exact ⟨l', ⟨hll', x, hl, hl'⟩, (Reach.adj (Hexagon.incGraph_adj_inr_inl.2 hl')).mono (by norm_num)⟩
          · exact ⟨l, ⟨Ne.symm hlℓ, x, h1', hl⟩, (Reach.adj (Hexagon.incGraph_adj_inr_inl.2 hl)).mono (by norm_num)⟩
        | cons h2 w2 =>
          rename_i b2
          cases b2 with
          | inl z => exact absurd h2 Hexagon.incGraph_not_adj_inl_inl
          | inr ℓ2 =>
            have h2' : inc y ℓ2 := Hexagon.incGraph_adj_inl_inr.1 h2
            simp only [Walk.length_cons] at hw
            by_cases he : ℓ = ℓ2
            · subst he
              exact ih (by omega) ℓ w2 (by omega)
            · exact ⟨ℓ2, ⟨he, y, h1', h2'⟩, w2, by omega⟩

/-- **Covering lemma.** -/
theorem cover (hP2 : ∀ p, ∃ l l', l ≠ l' ∧ inc p l ∧ inc p l') {ℓ : L} {x : P}
    (h : Reach (Hexagon.incGraph inc) (.inr ℓ) (.inl x) 5) :
    ∃ ℓ', Conc inc ℓ ℓ' ∧ Reach (Hexagon.incGraph inc) (.inr ℓ') (.inl x) 3 := by
  obtain ⟨w, hw⟩ := h
  exact cover_aux hP2 x 5 le_rfl ℓ w hw

theorem cover_dual_aux (hL2 : ∀ l, ∃ p p', p ≠ p' ∧ inc p l ∧ inc p' l) (m : L) :
    ∀ n, n ≤ 5 → ∀ (p : P) (w : (Hexagon.incGraph inc).Walk (.inl p) (.inr m)), w.length ≤ n →
      ∃ p', Coll inc p p' ∧ Reach (Hexagon.incGraph inc) (.inl p') (.inr m) 3 := by
  intro n
  induction n with
  | zero =>
    intro _ p w hw
    cases w with
    | cons h w' => simp at hw
  | succ n ih =>
    intro hn p w hw
    cases w with
    | cons h1 w1 =>
      rename_i b
      cases b with
      | inl z => exact absurd h1 Hexagon.incGraph_not_adj_inl_inl
      | inr l =>
        have h1' : inc p l := Hexagon.incGraph_adj_inl_inr.1 h1
        cases w1 with
        | nil =>
          obtain ⟨a, a', haa', ha, ha'⟩ := hL2 m
          by_cases hap : a = p
          · subst hap
            exact ⟨a', ⟨haa', m, ha, ha'⟩, (Reach.adj (Hexagon.incGraph_adj_inl_inr.2 ha')).mono (by norm_num)⟩
          · exact ⟨a, ⟨Ne.symm hap, m, h1', ha⟩, (Reach.adj (Hexagon.incGraph_adj_inl_inr.2 ha)).mono (by norm_num)⟩
        | cons h2 w2 =>
          rename_i b2
          cases b2 with
          | inr l2 => exact absurd h2 Hexagon.incGraph_not_adj_inr_inr
          | inl p2 =>
            have h2' : inc p2 l := Hexagon.incGraph_adj_inr_inl.1 h2
            simp only [Walk.length_cons] at hw
            by_cases he : p = p2
            · subst he
              exact ih (by omega) p w2 (by omega)
            · exact ⟨p2, ⟨he, l, h1', h2'⟩, w2, by omega⟩

/-- **Dual covering lemma.** -/
theorem cover_dual (hL2 : ∀ l, ∃ p p', p ≠ p' ∧ inc p l ∧ inc p' l) {p : P} {m : L}
    (h : Reach (Hexagon.incGraph inc) (.inl p) (.inr m) 5) :
    ∃ p', Coll inc p p' ∧ Reach (Hexagon.incGraph inc) (.inl p') (.inr m) 3 := by
  obtain ⟨w, hw⟩ := h
  exact cover_dual_aux hL2 m 5 le_rfl p w hw

/-- Two collinear points are joined by a walk of length `2`. -/
theorem Coll.reach {r p : P} (h : Coll inc r p) : Reach (Hexagon.incGraph inc) (.inl r) (.inl p) 2 := by
  obtain ⟨-, l, hr, hp⟩ := h
  exact (Reach.adj (Hexagon.incGraph_adj_inl_inr.2 hr)).trans (Reach.adj (Hexagon.incGraph_adj_inr_inl.2 hp))

/-- Two concurrent lines are joined by a walk of length `2`. -/
theorem Conc.reach {l l' : L} (h : Conc inc l l') : Reach (Hexagon.incGraph inc) (.inr l) (.inr l') 2 := by
  obtain ⟨-, p, hl, hl'⟩ := h
  exact (Reach.adj (Hexagon.incGraph_adj_inr_inl.2 hl)).trans (Reach.adj (Hexagon.incGraph_adj_inl_inr.2 hl'))

end BipartiteDD.HexagonD7
