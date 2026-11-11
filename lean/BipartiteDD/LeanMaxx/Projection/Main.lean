import BipartiteDD.LeanMaxx.Projection.Walk
import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Distance bound for the projection

Let `B` be a graph on `β`, `G` a graph on `V`, `f : V → β` a label map and `c : V → Option ι` a copy map.
Hypotheses `h1`, `h2`, `h3` are as in `Walk.lean`. A new vertex `x` (`c x = none`) that has no neighbour
in copy `j`, and a vertex `v` of copy `j`, are at `G`-distance at least `B.dist (f x) (f v) + 3`.
-/

namespace BipartiteDD.LeanMaxx.Projection

open SimpleGraph

variable {β V ι : Type*} {B : SimpleGraph β} {G : SimpleGraph V} {f : V → β} {c : V → Option ι}

/-- Every walk from a new vertex `x` to a copy vertex `v` of copy `j` has length at least
`B.dist (f x) (f v) + 3`. -/
theorem walk_ge
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {x v : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j)
    (hv : c v = some j) (p : G.Walk x v) :
    B.dist (f x) (f v) + 3 ≤ p.length := by
  have hvne : c v ≠ none := by rw [hv]; simp
  obtain ⟨q, hq⟩ := exists_label_walk h1 h2 h3 hvne p
  simp only [hx, ↓reduceIte] at hq
  -- The walk passes through a new vertex: otherwise its second vertex and its end share copy index `j`.
  have hK : 1 ≤ newCount c p := by
    cases p with
    | nil => exact absurd (hx.symm.trans hv) (by simp)
    | @cons _ u1 _ hxu p' =>
      by_contra hzero
      have hcopy : ∀ w ∈ p'.support, c w ≠ none := by
        intro w hw
        have h0 : newCount c (SimpleGraph.Walk.cons hxu p') = 0 := by omega
        unfold newCount at h0
        rw [SimpleGraph.Walk.support_cons, List.tail_cons, List.countP_eq_zero] at h0
        simpa using h0 w hw
      obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp (hcopy u1 (SimpleGraph.Walk.start_mem_support p'))
      have hij := copy_index_const h1 p' hcopy i j hi hv
      exact hmiss u1 hxu (hi.trans (congrArg some hij))
  have hdist := SimpleGraph.dist_le q
  omega

/-- **Projection theorem.** A new vertex `x` that has no neighbour in copy `j` is at `G`-edist at least
`B.dist (f x) (f v) + 3` from every vertex `v` of copy `j`. -/
theorem edist_ge
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {x v : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j)
    (hv : c v = some j) :
    (B.dist (f x) (f v) + 3 : ℕ∞) ≤ G.edist x v := by
  unfold SimpleGraph.edist
  refine le_iInf fun p => ?_
  exact_mod_cast walk_ge h1 h2 h3 hx hmiss hv p

/-- Distance version of `edist_ge`, for vertices joined by a walk. -/
theorem dist_ge
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {x v : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j)
    (hv : c v = some j) (hr : G.Reachable x v) :
    B.dist (f x) (f v) + 3 ≤ G.dist x v := by
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [← hp]
  exact walk_ge h1 h2 h3 hx hmiss hv p

/-- **Corollary.** If `B` has a pair `t, s` at distance `D₁` (any pair at the diameter of a connected
`B` will do), a new vertex `x` labelled `t` that has no neighbour in copy `j`, and a vertex `v` of copy `j`
labelled `s`, then `G` has diameter at least `D₁ + 3`. -/
theorem ediam_ge
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j → i = j ∧ B.Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none → c w ≠ none ∧ f w = f x)
    (h3 : ∀ x w, G.Adj x w → c x = none → c w = none → False)
    {D₁ : ℕ} {t s : β} (hts : B.edist t s = D₁)
    {x v : V} (hfx : f x = t) (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j)
    (hfv : f v = s) (hv : c v = some j) :
    (D₁ + 3 : ℕ∞) ≤ G.ediam := by
  have hr : B.Reachable t s := edist_ne_top_iff_reachable.mp (by rw [hts]; simp)
  have hd : B.dist t s = D₁ := by
    have h := hr.coe_dist_eq_edist
    rw [hts] at h
    exact_mod_cast h
  have key := edist_ge h1 h2 h3 hx hmiss hv
  rw [hfx, hfv, hd] at key
  exact key.trans edist_le_ediam

end BipartiteDD.LeanMaxx.Projection
