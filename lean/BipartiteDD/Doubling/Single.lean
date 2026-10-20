import BipartiteDD.Doubling.Core

/-! Group Doubling, part 2: single-level doubling (Delorme).

`double G A` has vertex type `V ⊕ A`: `inl v` is the original vertex `v`, and `inr a` is the copy `a'` of
`a ∈ A`. The edges are all edges of `G` on the originals, `a'b'` for every edge `ab` of `G` inside `A`, and
`a'w` for every edge `aw` of `G` with `w ∉ A`.

* bipartite if `G` is (`double_colorable`);
* maximum degree at most `Δ + 1` if `G` has maximum degree `Δ` and each vertex outside `A` has at most
  one neighbour in `A` (`double_degree`);
* diameter at most `D` if `G` has diameter at most `D` and (c) holds (`double_ediam`); `D ≥ 2` is not used
  by the proof: for `D ≤ 1` condition (c) is only satisfiable in degenerate cases.

The diameter proof uses two sheets. The map `φ₀ = inl` and the map `φ₁` (`v ↦ v'` for `v ∈ A`, `v ↦ v`
otherwise) are graph homomorphisms `G → double G A`, so each is distance non-increasing. A vertex outside
`A` lies in both sheets, which is how a walk is switched from one sheet to the other. -/

namespace BipartiteDD.Doubling

open SimpleGraph
open scoped Classical

variable {V : Type*}

/-- Delorme's doubling of `G` along `A`. -/
def double (G : SimpleGraph V) (A : Set V) : SimpleGraph (V ⊕ A) where
  Adj x y :=
    match x, y with
    | .inl u, .inl v => G.Adj u v
    | .inl w, .inr a => G.Adj w a.1 ∧ w ∉ A
    | .inr a, .inl w => G.Adj a.1 w ∧ w ∉ A
    | .inr a, .inr b => G.Adj a.1 b.1
  symm := ⟨fun x y h => by
    rcases x with u | a <;> rcases y with v | b
    · exact h.symm
    · exact ⟨h.1.symm, h.2⟩
    · exact ⟨h.1.symm, h.2⟩
    · exact h.symm⟩
  loopless := ⟨fun x h => by
    rcases x with u | a
    · exact G.irrefl h
    · exact G.irrefl h⟩

variable {G : SimpleGraph V} {A : Set V}

@[simp] theorem double_adj_inl_inl {u v : V} : (double G A).Adj (.inl u) (.inl v) ↔ G.Adj u v :=
  Iff.rfl

@[simp] theorem double_adj_inl_inr {w : V} {a : A} :
    (double G A).Adj (.inl w) (.inr a) ↔ G.Adj w a.1 ∧ w ∉ A := Iff.rfl

@[simp] theorem double_adj_inr_inl {a : A} {w : V} :
    (double G A).Adj (.inr a) (.inl w) ↔ G.Adj a.1 w ∧ w ∉ A := Iff.rfl

@[simp] theorem double_adj_inr_inr {a b : A} : (double G A).Adj (.inr a) (.inr b) ↔ G.Adj a.1 b.1 :=
  Iff.rfl

/-- The number of vertices of the doubling is `|V| + |A|`. -/
theorem card_double [Fintype V] [Fintype A] :
    Fintype.card (V ⊕ A) = Fintype.card V + Fintype.card A := Fintype.card_sum

/-! ### Bipartite -/

/-- The doubling of a bipartite graph is bipartite: a copy gets the colour of its original. -/
theorem double_colorable (hG : G.Colorable 2) : (double G A).Colorable 2 := by
  obtain ⟨c⟩ := hG
  refine ⟨SimpleGraph.Coloring.mk (fun v => Sum.elim c (fun a => c a.1) v) ?_⟩
  intro x y h
  rcases x with u | a <;> rcases y with v | b
  · exact c.valid h
  · exact c.valid h.1
  · exact c.valid h.1
  · exact c.valid h

/-! ### Degree -/

/-- Degree at most `Δ + 1`, when each vertex outside `A` has at most one neighbour in `A`. -/
theorem double_degree [Finite V] {Δ : ℕ} (hΔ : ∀ v, (G.neighborSet v).ncard ≤ Δ)
    (hb : ∀ v, v ∉ A → (G.neighborSet v ∩ A).ncard ≤ 1) (x : V ⊕ A) :
    ((double G A).neighborSet x).ncard ≤ Δ + 1 := by
  rcases x with v | a
  · -- an original: its neighbours in `G`, plus at most one copy
    have hsub : (double G A).neighborSet (.inl v) ⊆
        (Sum.inl '' G.neighborSet v) ∪ (Sum.inr '' {b : A | G.Adj v b.1 ∧ v ∉ A}) := by
      intro y hy
      rcases y with u | b
      · exact Or.inl ⟨u, hy, rfl⟩
      · exact Or.inr ⟨b, hy, rfl⟩
    have hT : ({b : A | G.Adj v b.1 ∧ v ∉ A}).ncard ≤ 1 := by
      by_cases hv : v ∈ A
      · have : {b : A | G.Adj v b.1 ∧ v ∉ A} = ∅ := by
          ext b
          simp [hv]
        rw [this]
        simp
      · rw [← Set.ncard_image_of_injective _ Subtype.val_injective]
        refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (hb v hv)
        rintro _ ⟨b, hb', rfl⟩
        exact ⟨hb'.1, b.2⟩
    calc ((double G A).neighborSet (.inl v)).ncard
        ≤ ((Sum.inl '' G.neighborSet v) ∪ (Sum.inr '' {b : A | G.Adj v b.1 ∧ v ∉ A})).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (Sum.inl '' G.neighborSet v).ncard + (Sum.inr '' {b : A | G.Adj v b.1 ∧ v ∉ A}).ncard :=
          Set.ncard_union_le _ _
      _ = (G.neighborSet v).ncard + ({b : A | G.Adj v b.1 ∧ v ∉ A}).ncard := by
          rw [Set.ncard_image_of_injective _ Sum.inl_injective,
            Set.ncard_image_of_injective _ Sum.inr_injective]
      _ ≤ Δ + 1 := Nat.add_le_add (hΔ v) hT
  · -- a copy: injects into the neighbours of its original
    let π : V ⊕ A → V := Sum.elim id Subtype.val
    refine le_trans (Set.ncard_le_ncard_of_injOn π ?_ ?_ (Set.toFinite _)) ((hΔ a.1).trans (by omega))
    · intro y hy
      rcases y with u | b
      · exact hy.1
      · exact hy
    · intro y hy y' hy' hyy'
      rcases y with u | b <;> rcases y' with u' | b'
      · simpa [π] using hyy'
      · have h1 : u ∉ A := hy.2
        have h2 : b'.1 ∈ A := b'.2
        simp only [π, Sum.elim_inl, Sum.elim_inr, id] at hyy'
        exact (h1 (hyy' ▸ h2)).elim
      · have h1 : u' ∉ A := hy'.2
        have h2 : b.1 ∈ A := b.2
        simp only [π, Sum.elim_inl, Sum.elim_inr, id] at hyy'
        exact (h1 (hyy' ▸ h2)).elim
      · have : b = b' := Subtype.ext (by simpa [π] using hyy')
        rw [this]

/-! ### Diameter -/

/-- The first sheet: the original copy of `G`. -/
def sheet0 (G : SimpleGraph V) (A : Set V) : G →g double G A where
  toFun := Sum.inl
  map_rel' := fun h => h

/-- The second sheet: vertices of `A` are replaced by their copies. -/
noncomputable def sheet1 (G : SimpleGraph V) (A : Set V) : G →g double G A where
  toFun v := if h : v ∈ A then .inr ⟨v, h⟩ else .inl v
  map_rel' := by
    intro u v h
    by_cases hu : u ∈ A <;> by_cases hv : v ∈ A <;> simp [hu, hv, h]

theorem sheet1_of_mem {v : V} (h : v ∈ A) : sheet1 G A v = .inr ⟨v, h⟩ := by
  simp [sheet1, h]

theorem sheet1_of_not_mem {v : V} (h : v ∉ A) : sheet1 G A v = .inl v := by
  simp [sheet1, h]

/-- Two vertices of the doubling are at distance at most `D` if `G` has diameter at most `D` and (c)
holds. -/
theorem double_edist_le {D : ℕ} (hD : G.ediam ≤ D) (hc : CondC G A D) (x y : V ⊕ A) :
    (double G A).edist x y ≤ D := by
  have hG : ∀ u v : V, G.edist u v ≤ D := fun u v => edist_le_ediam.trans hD
  -- from a vertex `inl v` to a copy `inr b`
  have key : ∀ (v : V) (b : A), (double G A).edist (.inl v) (.inr b) ≤ D := by
    intro v b
    by_cases hv : v ∈ A
    · obtain ⟨z, hz, hzD⟩ := exists_mid hc (hG v b.1)
      have h1 : (double G A).edist (.inl v) (.inl z) ≤ G.edist v z :=
        edist_le_of_hom (sheet0 G A) v z
      have h2 : (double G A).edist (.inl z) (.inr b) ≤ G.edist z b.1 := by
        have := edist_le_of_hom (sheet1 G A) z b.1
        rwa [sheet1_of_not_mem hz, sheet1_of_mem b.2] at this
      calc (double G A).edist (.inl v) (.inr b)
          ≤ (double G A).edist (.inl v) (.inl z) + (double G A).edist (.inl z) (.inr b) :=
            SimpleGraph.edist_triangle
        _ ≤ G.edist v z + G.edist z b.1 := add_le_add h1 h2
        _ ≤ D := hzD
    · have := edist_le_of_hom (sheet1 G A) v b.1
      rw [sheet1_of_not_mem hv, sheet1_of_mem b.2] at this
      exact this.trans (hG _ _)
  rcases x with u | a <;> rcases y with v | b
  · exact (edist_le_of_hom (sheet0 G A) u v).trans (hG _ _)
  · exact key u b
  · rw [edist_comm]
    exact key v a
  · have := edist_le_of_hom (sheet1 G A) a.1 b.1
    rw [sheet1_of_mem a.2, sheet1_of_mem b.2] at this
    exact this.trans (hG _ _)

/-- The doubling has diameter at most `D`. -/
theorem double_ediam {D : ℕ} (hD : G.ediam ≤ D) (hc : CondC G A D) : (double G A).ediam ≤ D :=
  ediam_le_iff.2 (double_edist_le hD hc)

/-! ### Main theorem -/

/-- Group Doubling, single level. If `G` is bipartite of maximum degree `Δ` and diameter at most `D`,
each vertex outside `A` has at most one neighbour in `A`, and (c) holds, then the doubling of `G` along `A`
is bipartite of maximum degree at most `Δ + 1` and diameter at most `D`. -/
theorem isBipartiteDegDiam_double [Finite V] {Δ D : ℕ} (hG : IsBipartiteDegDiam G Δ D)
    (hb : ∀ v, v ∉ A → (G.neighborSet v ∩ A).ncard ≤ 1) (hc : CondC G A D) :
    IsBipartiteDegDiam (double G A) (Δ + 1) D :=
  ⟨double_colorable hG.1, double_degree hG.2.1 hb, double_ediam hG.2.2 hc⟩

end BipartiteDD.Doubling
