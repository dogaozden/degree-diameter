import BipartiteDD.LeanMaxx.Omega45b.Defs
import BipartiteDD.LeanMaxx.Omega3.Concrete

/-!
# Omega45b: distance between points of `H(q)` is read off from the polar form

In the incidence graph `G = incGraph hexInc` of the split Cayley hexagon `H(F)` (`F` finite of odd
characteristic) two points `x y` satisfy

* `dist x y ≤ 4  ↔  Bf x y = 0`   (`dist_inl_le_four_iff_gen`),
* `dist x y = 6  ↔  Bf x y ≠ 0`   (`dist_inl_eq_six_iff_gen`),

and the same for `F7 = ZMod 7` with the graph `G7`.

(⇒ of the first) A walk of length `0, 2, 4` between points: the middle point `m` of a length-4 walk
has both ends on lines through `m`, hence in the totally singular plane `plane m`.
(⇐ of the first) `exists_mid`: two orthogonal singular points have a common neighbour in the collinearity
graph. The second statement follows from the parity and diameter facts of `Hex`.
No point counting is needed.
-/

set_option linter.unusedSectionVars false

namespace BipartiteDD.LeanMaxx.Omega45b

open BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega2

section general

variable {F : Type*} [Field F]

/-- The incidence graph of `H(F)`. -/
abbrev Ginc (F : Type*) [Field F] : SimpleGraph (SPt F ⊕ HLine F) :=
  BipartiteDD.Hexagon.incGraph (hexInc (F := F))

/-- Two points on a common line. -/
def Col (x y : SPt F) : Prop := ∃ W : HLine F, hexInc x W ∧ hexInc y W

theorem Col.bf_eq_zero {x y : SPt F} (h : Col x y) : Bf x.1.rep y.1.rep = 0 := by
  obtain ⟨W, hx, hy⟩ := h
  exact (W.2.2 _ hx _ hy).2.2.1

theorem Col.symm {x y : SPt F} (h : Col x y) : Col y x := by
  obtain ⟨W, hx, hy⟩ := h
  exact ⟨W, hy, hx⟩

theorem Bf_self_eq_zero (x : SPt F) : Bf x.1.rep x.1.rep = 0 := by
  have h := x.2
  simp only [Bf, Qf] at *
  linear_combination 2 * h

/-- If `x` and `y` are both collinear with `m`, then `Bf x y = 0`. -/
theorem bf_eq_zero_of_col_col {x m y : SPt F} (h1 : Col x m) (h2 : Col m y) :
    Bf x.1.rep y.1.rep = 0 := by
  obtain ⟨W1, hx, hm1⟩ := h1
  obtain ⟨W2, hm2, hy⟩ := h2
  have hm0 : m.1.rep ≠ 0 := m.1.rep_nonzero
  have hmQ : Qf m.1.rep = 0 := m.2
  have e1 : IsHPair m.1.rep x.1.rep := (W1.2.2 _ hm1 _ hx)
  have e2 : IsHPair m.1.rep y.1.rep := (W2.2.2 _ hm2 _ hy)
  rw [isHPair_iff_mem_plane hm0 hmQ] at e1 e2
  exact Bf_eq_zero_of_mem_plane hm0 e1 e2

/-- A walk of length `n + 2` between points: first two steps. -/
theorem walk_step2 {x y : SPt F} {n : ℕ} (w : (Ginc F).Walk (.inl x) (.inl y))
    (hw : w.length = n + 2) :
    ∃ (p : SPt F) (w' : (Ginc F).Walk (.inl p) (.inl y)), Col x p ∧ w'.length = n := by
  cases w with
  | nil => simp at hw
  | @cons _ v _ h1 w1 =>
    rcases v with p | l
    · exact (BipartiteDD.Hexagon.incGraph_not_adj_inl_inl h1).elim
    · cases w1 with
      | @cons _ v' _ h2 w2 =>
        rcases v' with p' | l'
        · refine ⟨p', w2, ⟨l, ?_, ?_⟩, ?_⟩
          · exact h1
          · exact h2
          · simpa using hw
        · exact (BipartiteDD.Hexagon.incGraph_not_adj_inr_inr h2).elim

theorem eq_of_walk_zero {x y : SPt F} (w : (Ginc F).Walk (.inl x) (.inl y)) (hw : w.length = 0) :
    x = y := by
  have := SimpleGraph.Walk.eq_of_length_eq_zero hw
  simpa using this

/-- A walk of length `0`, `2` or `4` between points forces `Bf = 0`. -/
theorem bf_eq_zero_of_walk {x y : SPt F} (w : (Ginc F).Walk (.inl x) (.inl y))
    (hw : w.length = 0 ∨ w.length = 2 ∨ w.length = 4) : Bf x.1.rep y.1.rep = 0 := by
  rcases hw with hw | hw | hw
  · rw [eq_of_walk_zero w hw]; exact Bf_self_eq_zero y
  · obtain ⟨p, w', h1, h2⟩ := walk_step2 (n := 0) w hw
    have := eq_of_walk_zero w' h2
    subst this
    exact h1.bf_eq_zero
  · obtain ⟨p, w', h1, h2⟩ := walk_step2 (n := 2) w hw
    obtain ⟨p', w'', h3, h4⟩ := walk_step2 (n := 0) w' h2
    have := eq_of_walk_zero w'' h4
    subst this
    exact bf_eq_zero_of_col_col h1 h3

section odd

variable [Fintype F] [NeZero (2 : F)]

/-- Orthogonal points are at distance at most `4` (a walk of length `4` through `exists_mid`). -/
theorem dist_le_four_of_bf {x y : SPt F} (h : Bf x.1.rep y.1.rep = 0) :
    (Ginc F).dist (.inl x) (.inl y) ≤ 4 := by
  obtain ⟨m, ⟨M1, h1x, h1m⟩, ⟨M2, h2m, h2w⟩⟩ :=
    exists_mid x.1.rep_nonzero x.2 y.1.rep_nonzero y.2 h
  have a1 : (Ginc F).Adj (Sum.inl x) (Sum.inr M1) := h1x
  have a2 : (Ginc F).Adj (Sum.inr M1) (Sum.inl m) := h1m
  have a3 : (Ginc F).Adj (Sum.inl m) (Sum.inr M2) := h2m
  have a4 : (Ginc F).Adj (Sum.inr M2) (Sum.inl y) := h2w
  have := SimpleGraph.dist_le (SimpleGraph.Walk.cons a1 (.cons a2 (.cons a3 (.cons a4 .nil))))
  simpa using this

/-- **Points at distance `≤ 4` in `H(F)` are exactly the orthogonal ones.** -/
theorem dist_inl_le_four_iff_gen (x y : SPt F) :
    (Ginc F).dist (Sum.inl x) (Sum.inl y) ≤ 4 ↔ Bf x.1.rep y.1.rep = 0 := by
  refine ⟨fun hd => ?_, dist_le_four_of_bf⟩
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  have hev : Even ((Ginc F).dist (Sum.inl x) (Sum.inl y)) :=
    dist_even_of_col H (u := Sum.inl x) (v := Sum.inl y) rfl
  obtain ⟨w, hw⟩ := (H.reach (Sum.inl x) (Sum.inl y)).exists_walk_length_eq_dist
  have hw' : w.length = (Ginc F).dist (Sum.inl x) (Sum.inl y) := hw
  apply bf_eq_zero_of_walk w
  obtain ⟨k, hk⟩ := hev
  omega

/-- **Points at distance `6` in `H(F)` are exactly the non-orthogonal ones.** -/
theorem dist_inl_eq_six_iff_gen (x y : SPt F) :
    (Ginc F).dist (Sum.inl x) (Sum.inl y) = 6 ↔ Bf x.1.rep y.1.rep ≠ 0 := by
  rw [Ne, ← dist_inl_le_four_iff_gen]
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  have hev : Even ((Ginc F).dist (Sum.inl x) (Sum.inl y)) :=
    dist_even_of_col H (u := Sum.inl x) (v := Sum.inl y) rfl
  have h6 : (Ginc F).dist (Sum.inl x) (Sum.inl y) ≤ 6 := H.diam (Sum.inl x) (Sum.inl y)
  obtain ⟨k, hk⟩ := hev
  omega

end odd

end general

/-! ### The concrete graph `G7 = incGraph hexInc` of `H(7)` -/

/-- The incidence graph of `H(7)`. -/
abbrev G7 : SimpleGraph (SPt F7 ⊕ HLine F7) := BipartiteDD.Hexagon.incGraph (hexInc (F := F7))

theorem dist_inl_le_four_iff (x y : SPt F7) :
    G7.dist (Sum.inl x) (Sum.inl y) ≤ 4 ↔ Bf x.1.rep y.1.rep = 0 := by
  have : NeZero (2 : F7) := ⟨by decide⟩
  exact dist_inl_le_four_iff_gen x y

theorem dist_inl_eq_six_iff (x y : SPt F7) :
    G7.dist (Sum.inl x) (Sum.inl y) = 6 ↔ Bf x.1.rep y.1.rep ≠ 0 := by
  have : NeZero (2 : F7) := ⟨by decide⟩
  exact dist_inl_eq_six_iff_gen x y

end BipartiteDD.LeanMaxx.Omega45b
