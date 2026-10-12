import BipartiteDD.Plus2.Degree
import BipartiteDD.Plus2.Graph

/-! Group E: the incidence graph of a frame is bipartite, has maximum degree `q + 2` and
diameter at most `3`; transporting it to `Fin (2 (q² + q + 6))` gives `plus2`. -/

namespace BipartiteDD.Plus2
open Configuration

namespace Frame

variable {P L : Type*} [Membership P L] [ProjectivePlane P L]
variable (F : Frame P L)

/-- Adjacent vertices of the incidence graph lie on opposite sides (points and lines). -/
theorem side_of_adj {u v : (P ⊕ NewPt) ⊕ (L ⊕ NewLn)} (h : F.graph.Adj u v) :
    u.isLeft ≠ v.isLeft := by
  rcases u with p | l <;> rcases v with q | m
  · exact (show False from h).elim
  · decide
  · decide
  · exact (show False from h).elim

/-- The incidence graph is 2-colourable. -/
theorem colorable : F.graph.Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) (by
    intro u v h
    have hne := F.side_of_adj h
    cases hu : u.isLeft <;> cases hv : v.isLeft <;> simp_all)⟩

/-- Every line has a point on it. -/
theorem exists_pt_on (l : L ⊕ NewLn) : ∃ p : P ⊕ NewPt, F.inc p l := by
  obtain ⟨m, hm⟩ : ∃ m : L ⊕ NewLn, m ≠ l := by
    by_cases h : l = .inr .M
    · exact ⟨.inr (.K .ra), fun e => by
        have := e.trans h
        cases this⟩
    · exact ⟨.inr .M, fun e => h e.symm⟩
  obtain ⟨p, hp, -⟩ := F.concurrent l m (Ne.symm hm)
  exact ⟨p, hp⟩

/-- Diameter at most 3, for the incidence graph itself. -/
theorem ediam_le : F.graph.ediam ≤ 3 :=
  ediam_le_three F.graph (Equiv.refl _) F.inc (fun _ _ => Iff.rfl)
    (fun p q h => F.collinear p q h) (fun l m h => F.concurrent l m h) (fun l => F.exists_pt_on l)

/-- Diameter at most 3, for the transport of the incidence graph along an equivalence. -/
theorem ediam_le_comap {W : Type*} (e : ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) ≃ W) :
    (F.graph.comap e.symm).ediam ≤ 3 :=
  ediam_le_three (F.graph.comap e.symm) e F.inc
    (fun a b => by
      rw [SimpleGraph.comap_adj, e.symm_apply_apply, e.symm_apply_apply]
      exact Iff.rfl)
    (fun p q h => F.collinear p q h) (fun l m h => F.concurrent l m h) (fun l => F.exists_pt_on l)

/-- The degree of a vertex of the transported graph is the degree of its preimage. -/
theorem degree_comap {W : Type*} (e : ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) ≃ W) (w : W) :
    ((F.graph.comap e.symm).neighborSet w).ncard = (F.graph.neighborSet (e.symm w)).ncard := by
  have hset : (F.graph.comap e.symm).neighborSet w =
      e.symm ⁻¹' (F.graph.neighborSet (e.symm w)) := by
    ext w'
    exact Iff.rfl
  rw [hset, Set.ncard_preimage_of_injective_subset_range e.symm.injective]
  rw [e.symm.surjective.range_eq]
  exact Set.subset_univ _

/-- The transported incidence graph is bipartite with degree `≤ q + 2` and diameter `≤ 3`. -/
theorem isBipartiteDegDiam_comap {W : Type*} (e : ((P ⊕ NewPt) ⊕ (L ⊕ NewLn)) ≃ W) :
    IsBipartiteDegDiam (F.graph.comap e.symm) (order P L + 2) 3 := by
  refine ⟨?_, fun w => ?_, F.ediam_le_comap e⟩
  · exact ⟨SimpleGraph.Coloring.mk (fun w => if (e.symm w).isLeft then (0 : Fin 2) else 1) (by
      intro u v h
      have hne := F.side_of_adj h
      cases hu : (e.symm u).isLeft <;> cases hv : (e.symm v).isLeft <;> simp_all)⟩
  · rw [F.degree_comap e w]
    exact F.degree_bound _

end Frame

/-- Group E, main theorem: the incidence graph of a frame, viewed on `P ⊕ NewPt ⊕ L ⊕ NewLn`,
is bipartite with maximum degree `q + 2` and diameter at most `3`. -/
theorem Frame.isBipartiteDegDiam {P L : Type*} [Membership P L] [ProjectivePlane P L]
    [Fintype P] [Fintype L] (F : Frame P L) :
    IsBipartiteDegDiam F.graph (ProjectivePlane.order P L + 2) 3 :=
  ⟨F.colorable, fun v => F.degree_bound v, by exact_mod_cast F.ediam_le⟩

/-- The `+2` theorem: for any finite projective plane with a frame, there is a graph on
`2 (q² + q + 6)` vertices that is bipartite, has maximum degree `q + 2` and diameter at most `3`. -/
theorem plus2 {P L : Type*} [Membership P L] [ProjectivePlane P L] [Fintype P] [Fintype L]
    (F : Frame P L) :
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

end BipartiteDD.Plus2
