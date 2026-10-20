import BipartiteDD.Regular.Defs

/-! Regularity, part 1c: the twin lemma.

Two vertices are twins when they have the same neighbourhood. Deleting a set `S` of vertices on one side,
each of which still has a twin outside `S`, does not increase any distance among the remaining vertices:
a walk through a deleted vertex can be rerouted through its surviving twin.

The statement is for the bipartite graph `biGraph r` of a relation `r : α → β → Prop`, deleting vertices
of the side `β`. The remaining graph is `biGraph (restrictR r S)` on `α ⊕ {b // b ∉ S}`. -/

namespace BipartiteDD.Regular

open SimpleGraph

variable {α β : Type*}

/-- The relation `r` restricted to the vertices of `β` outside `S`. -/
def restrictR (r : α → β → Prop) (S : Set β) : α → {b // b ∉ S} → Prop := fun a b => r a b.1

/-- The inclusion of the remaining graph into the whole graph. -/
def embHom (r : α → β → Prop) (S : Set β) : biGraph (restrictR r S) →g biGraph r where
  toFun := Sum.map id Subtype.val
  map_rel' := by
    intro u v h
    rcases u with a | b <;> rcases v with a' | b'
    · exact (biGraph_adj_inl_inl _ a a' h).elim
    · exact h
    · exact h
    · exact (biGraph_adj_inr_inr _ b b' h).elim

/-- The retraction: every deleted vertex goes to a surviving twin, every other vertex stays. -/
noncomputable def twinMap (r : α → β → Prop) (S : Set β) (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b)
    (b : β) : {b // b ∉ S} :=
  open Classical in
  if h : b ∈ S then ⟨(htwin b h).choose, (htwin b h).choose_spec.1⟩ else ⟨b, h⟩

theorem twinMap_spec (r : α → β → Prop) (S : Set β) (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b)
    (b : β) (a : α) : r a (twinMap r S htwin b).1 ↔ r a b := by
  unfold twinMap
  by_cases h : b ∈ S
  · simp only [h, ↓reduceDIte]
    exact (htwin b h).choose_spec.2 a
  · simp only [h, ↓reduceDIte]

theorem twinMap_of_notMem (r : α → β → Prop) (S : Set β) (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b)
    (b : {b // b ∉ S}) : twinMap r S htwin b.1 = b := by
  unfold twinMap
  simp only [b.2, ↓reduceDIte]

/-- The retraction is a graph homomorphism. -/
noncomputable def retractHom (r : α → β → Prop) (S : Set β)
    (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b) : biGraph r →g biGraph (restrictR r S) where
  toFun := Sum.map id (twinMap r S htwin)
  map_rel' := by
    intro u v h
    rcases u with a | b <;> rcases v with a' | b'
    · exact (biGraph_adj_inl_inl _ a a' h).elim
    · exact (twinMap_spec r S htwin b' a).2 h
    · exact (twinMap_spec r S htwin b a').2 h
    · exact (biGraph_adj_inr_inr _ b b' h).elim

/-- The twin lemma: distances among the remaining vertices do not increase when each deleted vertex
has a surviving twin. -/
theorem edist_restrict_le (r : α → β → Prop) (S : Set β)
    (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b)
    (x y : α ⊕ {b // b ∉ S}) :
    (biGraph (restrictR r S)).edist x y ≤
      (biGraph r).edist (Sum.map id Subtype.val x) (Sum.map id Subtype.val y) := by
  have h := edist_le_of_hom (retractHom r S htwin) (Sum.map id Subtype.val x)
    (Sum.map id Subtype.val y)
  have hx : retractHom r S htwin (Sum.map id Subtype.val x) = x := by
    rcases x with a | b
    · rfl
    · exact congrArg Sum.inr (twinMap_of_notMem r S htwin b)
  have hy : retractHom r S htwin (Sum.map id Subtype.val y) = y := by
    rcases y with a | b
    · rfl
    · exact congrArg Sum.inr (twinMap_of_notMem r S htwin b)
  rw [hx, hy] at h
  exact h

/-- The diameter of the graph after deleting vertices that keep a twin is at most the old diameter. -/
theorem ediam_restrict_le (r : α → β → Prop) (S : Set β)
    (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b) :
    (biGraph (restrictR r S)).ediam ≤ (biGraph r).ediam := by
  rw [ediam_le_iff]
  intro x y
  exact (edist_restrict_le r S htwin x y).trans edist_le_ediam

/-- The diameter bound passes to the remaining graph. -/
theorem ediam_restrict_le_of_le (r : α → β → Prop) (S : Set β)
    (htwin : ∀ b ∈ S, ∃ b' ∉ S, ∀ a, r a b' ↔ r a b) {D : ℕ∞} (h : (biGraph r).ediam ≤ D) :
    (biGraph (restrictR r S)).ediam ≤ D :=
  (ediam_restrict_le r S htwin).trans h

/-- The twin lemma for a single deleted vertex `b`, which has a twin `b'` (`b' ≠ b`, same neighbourhood). -/
theorem ediam_restrict_singleton_le (r : α → β → Prop) (b b' : β) (hne : b' ≠ b)
    (htw : ∀ a, r a b' ↔ r a b) :
    (biGraph (restrictR r {b})).ediam ≤ (biGraph r).ediam :=
  ediam_restrict_le r {b} (fun c hc => by
    rw [Set.mem_singleton_iff] at hc
    subst hc
    exact ⟨b', hne, htw⟩)

/-- Twin classes: if the vertices of each class `cls b = k` all have the same neighbourhood, and
`S` contains fewer than all vertices of each class, then every deleted vertex has a surviving twin. -/
theorem htwin_of_classes {κ : Type*} [Fintype β] [DecidableEq κ] (r : α → β → Prop) (cls : β → κ)
    (hcls : ∀ b b', cls b = cls b' → ∀ a, r a b ↔ r a b') (S : Finset β)
    (hS : ∀ k, (S.filter (fun b => cls b = k)).card < (Finset.univ.filter (fun b => cls b = k)).card) :
    ∀ b ∈ (S : Set β), ∃ b' ∉ (S : Set β), ∀ a, r a b' ↔ r a b := by
  classical
  intro b _
  have hlt := hS (cls b)
  have hsub : S.filter (fun c => cls c = cls b) ⊆ Finset.univ.filter (fun c => cls c = cls b) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  obtain ⟨b', hb', hb'S⟩ := Finset.exists_of_ssubset
    (Finset.ssubset_iff_subset_ne.2 ⟨hsub, fun h => by rw [h] at hlt; exact lt_irrefl _ hlt⟩)
  have hcb' : cls b' = cls b := (Finset.mem_filter.1 hb').2
  refine ⟨b', fun hmem => hb'S (Finset.mem_filter.2 ⟨by exact_mod_cast hmem, hcb'⟩), fun a => ?_⟩
  exact hcls b' b hcb' a

end BipartiteDD.Regular
