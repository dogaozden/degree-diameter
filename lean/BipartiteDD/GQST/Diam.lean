import BipartiteDD.GQST.Defs
import Mathlib.Tactic.NormNum

/-! Group GQST, part 2: the incidence graph of a generalized quadrangle of order `(s, t)` has diameter
at most `4`. The argument is that of `GQ.ediam_le_four`; only the axioms are used, not the parameters.
A point and a line are at distance at most `3`; two points or two lines at distance at most `4`. -/

namespace BipartiteDD

open SimpleGraph

variable {P L : Type*} [Membership P L] {s t : ℕ}

namespace GQst

/-- A point and a line are at distance at most `3` in the incidence graph. -/
theorem edist_pt_line_le (G : GQst P L s t) (p : P) (l : L) :
    (incGraph P L).edist (.inl p) (.inr l) ≤ 3 := by
  by_cases h : p ∈ l
  · exact (edist_le (Walk.cons (incGraph_adj_inl_inr.2 h) Walk.nil)).trans (by simp)
  · obtain ⟨x, hxl, m, hpm, hxm⟩ := G.gq_ax p l h
    let w : (incGraph P L).Walk (.inl p) (.inr l) :=
      Walk.cons (incGraph_adj_inl_inr.2 hpm)
        (Walk.cons (incGraph_adj_inr_inl.2 hxm)
          (Walk.cons (incGraph_adj_inl_inr.2 hxl) Walk.nil))
    exact (edist_le w).trans (by simp [w])

/-- The incidence graph of a generalized quadrangle of order `(s, t)` has diameter at most `4`. -/
theorem ediam_le_four (G : GQst P L s t) : (incGraph P L).ediam ≤ 4 := by
  rw [ediam_le_iff]
  rintro (p | l) (r | m)
  · -- two points: step to a line through the second point
    obtain ⟨l, hl⟩ := G.exists_line r
    calc (incGraph P L).edist (.inl p) (.inl r)
        ≤ (incGraph P L).edist (.inl p) (.inr l) + (incGraph P L).edist (.inr l) (.inl r) :=
          SimpleGraph.edist_triangle
      _ ≤ 3 + 1 := by
          refine add_le_add (G.edist_pt_line_le p l) ?_
          exact (edist_le (Walk.cons (incGraph_adj_inr_inl.2 hl) Walk.nil)).trans (by simp)
      _ = 4 := by norm_num
  · -- point and line
    exact (G.edist_pt_line_le p m).trans (by norm_num)
  · -- line and point
    rw [edist_comm]
    exact (G.edist_pt_line_le r l).trans (by norm_num)
  · -- two lines: step to a point on the first line
    obtain ⟨p, hp⟩ := G.exists_pt l
    calc (incGraph P L).edist (.inr l) (.inr m)
        ≤ (incGraph P L).edist (.inr l) (.inl p) + (incGraph P L).edist (.inl p) (.inr m) :=
          SimpleGraph.edist_triangle
      _ ≤ 1 + 3 := by
          refine add_le_add ?_ (G.edist_pt_line_le p m)
          exact (edist_le (Walk.cons (incGraph_adj_inr_inl.2 hp) Walk.nil)).trans (by simp)
      _ = 4 := by norm_num

end GQst

end BipartiteDD
