import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Walks in a projected graph

Setting: `B` is a graph on a type `β`, `G` a graph on `V`, `f : V → β` is a label map and
`c : V → Option ι` a copy map (`some i` = vertex of copy `i`, `none` = new vertex). The hypotheses are

* `h1`: a `G`-edge between two copy vertices stays inside one copy and projects to a `B`-edge;
* `h2`: a new vertex is adjacent only to copy vertices carrying its own label;
* `h3`: no two new vertices are adjacent.

The lemmas here are the walk-level part of the projection argument.
-/

namespace BipartiteDD.LeanMaxx.Projection

open SimpleGraph

variable {β V ι : Type*} {B : SimpleGraph β} {G : SimpleGraph V} {f : V → β} {c : V → Option ι}

/-- A walk whose vertices are all copy vertices keeps one copy index from start to end. -/
theorem copy_index_const
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    {a b : V} (p : G.Walk a b) (hcopy : ∀ w ∈ p.support, c w ≠ none)
    (i j : ι) (hi : c a = some i) (hj : c b = some j) : i = j := by
  induction p generalizing i with
  | nil => simpa [hi] using hj
  | @cons a a' _ h p ih =>
    obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp (hcopy a' (by simp))
    have hstep := (h1 a a' i i' h hi hi').1
    have hrest := ih (fun w hw => hcopy w (by simp [hw])) i' hi' hj
    exact hstep.trans hrest

/-- The number of new vertices a walk passes through, not counting its starting vertex. -/
def newCount (c : V → Option ι) {a b : V} (p : G.Walk a b) : ℕ :=
  p.support.tail.countP fun w => decide (c w = none)

/-- Projection bound. A walk from `a` to a copy vertex `b` projects to a walk from `f a` to `f b`
in `B`, and its length pays 2 for each new vertex it passes through, plus 1 if it starts at a new
vertex. Induction on the walk, one edge at a time. -/
theorem exists_label_walk
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {a b : V} (hb : c b ≠ none) (p : G.Walk a b) :
    ∃ q : B.Walk (f a) (f b),
      q.length + 2 * newCount c p + (if c a = none then 1 else 0) ≤ p.length := by
  induction p with
  | nil => exact ⟨.nil, by simp [newCount, hb]⟩
  | @cons a a' _ h p ih =>
    obtain ⟨q', hq'⟩ := ih hb
    have hK : newCount c (SimpleGraph.Walk.cons h p) =
        (if c a' = none then 1 else 0) + newCount c p := by
      have hsup : p.support = a' :: p.support.tail := (SimpleGraph.Walk.cons_tail_support p).symm
      unfold newCount
      rw [SimpleGraph.Walk.support_cons, List.tail_cons]
      conv_lhs => rw [hsup]
      rw [List.countP_cons]
      simp only [decide_eq_true_eq]
      exact Nat.add_comm _ _
    rw [hK]
    by_cases ha : c a = none <;> by_cases ha' : c a' = none
    · exact (h3 a a' h ha ha').elim
    · obtain ⟨hcopy, hf⟩ := h2 a a' h ha
      refine ⟨q'.copy hf rfl, ?_⟩
      simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons, ha, ha',
        ↓reduceIte] at hq' ⊢
      omega
    · obtain ⟨hcopy, hf⟩ := h2 a' a h.symm ha'
      refine ⟨q'.copy hf.symm rfl, ?_⟩
      simp only [SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_cons, ha, ha',
        ↓reduceIte] at hq' ⊢
      omega
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp ha
      obtain ⟨i', hi'⟩ := Option.ne_none_iff_exists'.mp ha'
      have hBadj := (h1 a a' i i' h hi hi').2
      refine ⟨SimpleGraph.Walk.cons hBadj q', ?_⟩
      simp only [SimpleGraph.Walk.length_cons, ha, ha', ↓reduceIte] at hq' ⊢
      omega

end BipartiteDD.LeanMaxx.Projection
