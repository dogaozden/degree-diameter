import BipartiteDD.GQST.Regular
import BipartiteDD.GQ4.Main

/-! Regularity, part 1a: the regular versions of the predicates, and the bipartite graph of a relation.

`IsRegularOfDegree G Δ` says every vertex has exactly `Δ` neighbours. `IsBipartiteRegDiam G Δ D` is the
regular analogue of `IsBipartiteDegDiam G Δ D`: bipartite, every degree exactly `Δ`, diameter at most `D`.

`Regular.biGraph r` is the bipartite graph on `α ⊕ β` in which `inl a` and `inr b` are adjacent exactly
when `r a b`. Every incidence graph in this development is of this shape. -/

namespace BipartiteDD

/-- Every vertex of `G` has exactly `Δ` neighbours. -/
def IsRegularOfDegree {V : Type*} (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, (G.neighborSet v).ncard = Δ

/-- `G` is bipartite, every vertex has exactly `Δ` neighbours, and every two vertices are joined by a walk
of length at most `D`. The regular version of `IsBipartiteDegDiam`. -/
def IsBipartiteRegDiam {V : Type*} (G : SimpleGraph V) (Δ D : ℕ) : Prop :=
  G.Colorable 2 ∧ IsRegularOfDegree G Δ ∧ G.ediam ≤ D

/-- A regular bipartite graph of diameter at most `D` is in particular one of maximum degree `Δ`. -/
theorem IsBipartiteRegDiam.toDegDiam {V : Type*} {G : SimpleGraph V} {Δ D : ℕ}
    (h : IsBipartiteRegDiam G Δ D) : IsBipartiteDegDiam G Δ D :=
  ⟨h.1, fun v => (h.2.1 v).le, h.2.2⟩

/-- Transport along a bijection. -/
theorem IsBipartiteRegDiam.comap {V V' : Type*} {G : SimpleGraph V} {Δ D : ℕ}
    (h : IsBipartiteRegDiam G Δ D) (e : V ≃ V') : IsBipartiteRegDiam (G.comap e.symm) Δ D := by
  obtain ⟨h1, h2, h3⟩ := GQST.regular_comap e G Δ h.1 h.2.1 h.2.2
  exact ⟨h1, h2, h3⟩

/-- Adding edges keeps a regular bipartite graph's diameter bound (the degrees must be re-checked). -/
theorem IsBipartiteRegDiam.mono {V : Type*} {G H : SimpleGraph V} {Δ D : ℕ} (hGH : G ≤ H)
    (hcol : H.Colorable 2) (hreg : IsRegularOfDegree H Δ) (hG : G.ediam ≤ D) :
    IsBipartiteRegDiam H Δ D :=
  ⟨hcol, hreg, ediam_le_of_le hGH hG⟩

/-- A regular bipartite graph on a finite type, transported to `Fin (Fintype.card V)`. -/
theorem IsBipartiteRegDiam.exists_fin {V : Type*} [Fintype V] {G : SimpleGraph V} {Δ D : ℕ}
    (h : IsBipartiteRegDiam G Δ D) :
    ∃ H : SimpleGraph (Fin (Fintype.card V)), IsBipartiteRegDiam H Δ D :=
  ⟨G.comap (Fintype.equivFin V).symm, h.comap (Fintype.equivFin V)⟩

namespace Regular

section BiGraph

variable {α β : Type*}

/-- The bipartite graph of a relation: `inl a` is adjacent to `inr b` exactly when `r a b`. -/
def biGraph (r : α → β → Prop) : SimpleGraph (α ⊕ β) where
  Adj u v := match u, v with
    | .inl a, .inr b => r a b
    | .inr b, .inl a => r a b
    | _, _ => False
  symm := ⟨fun u v h => by
    rcases u with a | b <;> rcases v with a' | b' <;> exact h⟩
  loopless := ⟨fun u h => by
    rcases u with a | b <;> exact h⟩

@[simp] theorem biGraph_adj_inl_inr (r : α → β → Prop) (a : α) (b : β) :
    (biGraph r).Adj (.inl a) (.inr b) ↔ r a b := Iff.rfl

@[simp] theorem biGraph_adj_inr_inl (r : α → β → Prop) (a : α) (b : β) :
    (biGraph r).Adj (.inr b) (.inl a) ↔ r a b := Iff.rfl

@[simp] theorem biGraph_adj_inl_inl (r : α → β → Prop) (a a' : α) :
    ¬ (biGraph r).Adj (.inl a) (.inl a') := fun h => h

@[simp] theorem biGraph_adj_inr_inr (r : α → β → Prop) (b b' : β) :
    ¬ (biGraph r).Adj (.inr b) (.inr b') := fun h => h

/-- The bipartite graph of a relation is 2-colourable. -/
theorem biGraph_colorable (r : α → β → Prop) : (biGraph r).Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) (by
    intro u v h
    rcases u with a | b <;> rcases v with a' | b'
    · exact (biGraph_adj_inl_inl r a a' h).elim
    · simp
    · simp
    · exact (biGraph_adj_inr_inr r b b' h).elim)⟩

/-- A bigger relation gives a bigger graph. -/
theorem biGraph_mono {r r' : α → β → Prop} (h : ∀ a b, r a b → r' a b) :
    biGraph r ≤ biGraph r' := by
  intro u v huv
  rcases u with a | b <;> rcases v with a' | b'
  · exact (biGraph_adj_inl_inl r a a' huv).elim
  · exact h _ _ huv
  · exact h _ _ huv
  · exact (biGraph_adj_inr_inr r b b' huv).elim

theorem neighborSet_inl (r : α → β → Prop) (a : α) :
    (biGraph r).neighborSet (.inl a) = Sum.inr '' {b | r a b} := by
  ext w
  rcases w with a' | b
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h => (biGraph_adj_inl_inl r a a' h).elim, fun ⟨_, _, h⟩ => by cases h⟩
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨b, h, rfl⟩, fun ⟨b', hb', h⟩ => by cases h; exact hb'⟩

theorem neighborSet_inr (r : α → β → Prop) (b : β) :
    (biGraph r).neighborSet (.inr b) = Sum.inl '' {a | r a b} := by
  ext w
  rcases w with a | b'
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨a, h, rfl⟩, fun ⟨a', ha', h⟩ => by cases h; exact ha'⟩
  · simp only [SimpleGraph.mem_neighborSet, Set.mem_image, Set.mem_ofPred_eq]
    exact ⟨fun h => (biGraph_adj_inr_inr r b b' h).elim, fun ⟨_, _, h⟩ => by cases h⟩

theorem ncard_neighborSet_inl (r : α → β → Prop) (a : α) :
    ((biGraph r).neighborSet (.inl a)).ncard = {b | r a b}.ncard := by
  rw [neighborSet_inl, Set.ncard_image_of_injective _ Sum.inr_injective]

theorem ncard_neighborSet_inr (r : α → β → Prop) (b : β) :
    ((biGraph r).neighborSet (.inr b)).ncard = {a | r a b}.ncard := by
  rw [neighborSet_inr, Set.ncard_image_of_injective _ Sum.inl_injective]

/-- Regularity of `biGraph r` in terms of the two sides. -/
theorem biGraph_regular_iff (r : α → β → Prop) (Δ : ℕ) :
    IsRegularOfDegree (biGraph r) Δ ↔ (∀ a, {b | r a b}.ncard = Δ) ∧ (∀ b, {a | r a b}.ncard = Δ) := by
  constructor
  · intro h
    exact ⟨fun a => by rw [← ncard_neighborSet_inl]; exact h _,
      fun b => by rw [← ncard_neighborSet_inr]; exact h _⟩
  · rintro ⟨h1, h2⟩ v
    rcases v with a | b
    · rw [ncard_neighborSet_inl]; exact h1 a
    · rw [ncard_neighborSet_inr]; exact h2 b

end BiGraph

end Regular

end BipartiteDD
