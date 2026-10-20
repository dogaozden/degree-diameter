import BipartiteDD.Plus2Zero.Exists

/-! The zero-change `+2` theorem. For every projective plane of order `q ≥ 3` there is a graph on
`2 (q² + q + 6)` vertices that is bipartite, has maximum degree `q + 2` and diameter at most `3`.
The plane's own incidence graph is an induced subgraph of it. -/

namespace BipartiteDD.Plus2Zero
open Configuration

/-- The incidence graph of the plane: points on the left, lines on the right. -/
def planeGraph (P L : Type*) [Membership P L] : SimpleGraph (P ⊕ L) where
  Adj u v := match u, v with
    | .inl p, .inr l => p ∈ l
    | .inr l, .inl p => p ∈ l
    | _, _ => False
  symm := ⟨fun u v h => by
    rcases u with p | l <;> rcases v with q | m <;> first | exact h | exact (show False from h).elim⟩
  loopless := ⟨fun u h => by
    rcases u with p | l <;> exact h⟩

namespace Frame

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]

/-- The plane's incidence graph is an induced subgraph of the zero-change graph: every incidence
of the plane is kept, and no other pair of plane vertices becomes adjacent. -/
theorem planeGraph_induced (F : Frame P L) (u v : P ⊕ L) :
    F.graph.Adj (Sum.map Sum.inl Sum.inl u) (Sum.map Sum.inl Sum.inl v) ↔
      (planeGraph P L).Adj u v := by
  rcases u with p | l <;> rcases v with q | m
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl
  · exact Iff.rfl

variable [Fintype P] [Fintype L]

/-- The transported incidence graph, on `Fin (2 (q² + q + 6))`. -/
theorem plus2zero (F : Frame P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteDegDiam G (ProjectivePlane.order P L + 2) 3 := by
  have hcard : Fintype.card ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) =
      2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6) := by
    have h5 : Fintype.card NewPt = 5 := rfl
    have h5' : Fintype.card NewLn = 5 := rfl
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_sum, h5, h5',
      ProjectivePlane.card_points P L, ProjectivePlane.card_lines P L]
    ring
  let e : ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) ≃ Fin (2 * (ProjectivePlane.order P L ^ 2 +
      ProjectivePlane.order P L + 6)) := Fintype.equivFinOfCardEq hcard
  exact ⟨F.graph.comap e.symm, F.isBipartiteDegDiam_comap e⟩

end Frame

/-- The zero-change `+2` theorem: for every finite projective plane of order `q ≥ 3`, there is a
graph on `2 (q² + q + 6)` vertices that is bipartite, has maximum degree `q + 2` and diameter at
most `3`. -/
theorem zero_isBipartiteDegDiam {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Fintype L] (h : 3 ≤ ProjectivePlane.order P L) :
    ∃ G : SimpleGraph (Fin (2 * (ProjectivePlane.order P L ^ 2 + ProjectivePlane.order P L + 6))),
      IsBipartiteDegDiam G (ProjectivePlane.order P L + 2) 3 := by
  obtain ⟨F⟩ := Frame.exists h
  exact F.plus2zero

end BipartiteDD.Plus2Zero
