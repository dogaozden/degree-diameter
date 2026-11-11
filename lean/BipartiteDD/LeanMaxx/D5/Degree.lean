import BipartiteDD.LeanMaxx.D5.ThmA
import BipartiteDD.GQ4.Main

/-! # D = 5 formalisation, part 5: colouring, degrees and order of `X_R^+`

`research/theorems/D5_QUADRANGLE.md` Definition 3.1 and Theorem 3.5, the counting half. Over a quadrangle of order
`(q, q)` with `2r + 1` levels (a regular tournament, `Surg`), freed sets `R i j` and hubs that take every freed slot
at most once (`arcV`, `arcU` with their injectivity), and a hub graph of maximum degree `≤ q - r`:

* `X` is bipartite (`Hyp.colorable`),
* every vertex has at most `q + 1 + r` neighbours (`Surg.degree_le`),
* `X` has `(2r + 1)(|P| + |L|) + |V| + |U|` vertices (`card_vtx`).

`Hyp.exists_graph` combines this with `Hyp.ediam_le_five` (Theorem 3.5/3.6) into a graph on `Fin n`. -/

namespace BipartiteDD.LeanMaxx.D5

set_option linter.unusedSectionVars false

open SimpleGraph BipartiteDD Finset
open scoped Classical

variable {P L : Type*} [Membership P L] {ι V U : Type*}

/-- The slot and tournament data of Definition 3.1 for `2r+1` levels over a quadrangle of order `(q, q)`:

* `T` is a regular tournament (`outdeg`), every freed slot is taken by at most one hub: the `𝓑`-hub `v` takes, at
  level `i`, the slot `(slotV v i, arcV v i)`, a freed element of the arc `i → arcV v i`; the `𝓐`-hub `u` takes at
  level `i` the freed `𝓑`-slot `(M ..)(slotU u i)` of the arc `arcU u i → i`;
* the hub graph has maximum degree at most `q - r` (`hubV`, `hubU`, written `deg + r ≤ q`). -/
structure Surg [Fintype ι] [Fintype V] [Fintype U] (D : Data P L ι V U) (q r : ℕ) where
  card_ι : Fintype.card ι = 2 * r + 1
  anti : ∀ i j, D.T i j → ¬ D.T j i
  outdeg : ∀ i, (univ.filter (D.T i)).card = r
  arcV : V → ι → ι
  arcV_T : ∀ v i, D.T i (arcV v i)
  arcV_R : ∀ v i, D.slotV v i ∈ D.R i (arcV v i)
  arcV_inj : ∀ v v' i, D.slotV v i = D.slotV v' i → arcV v i = arcV v' i → v = v'
  arcU : U → ι → ι
  arcU_T : ∀ u i, D.T (arcU u i) i
  arcU_R : ∀ u i, (D.M (arcU u i) i).symm (D.slotU u i) ∈ D.R (arcU u i) i
  arcU_inj : ∀ u u' i, D.slotU u i = D.slotU u' i → arcU u i = arcU u' i → u = u'
  hubV : ∀ v, (univ.filter (D.NS v)).card + r ≤ q
  hubU : ∀ u, (univ.filter (fun v => D.NS v u)).card + r ≤ q

section Counting

variable [Fintype P] [Fintype L] [Fintype ι] [Fintype V] [Fintype U]

theorem card_nbr_le {q : ℕ} (G : GQst P L q q) (x : P ⊕ L) :
    (univ.filter (fun y => (incGraph P L).Adj x y)).card ≤ q + 1 := by
  rcases x with p | l
  · have : univ.filter (fun y : P ⊕ L => (incGraph P L).Adj (.inl p) y) ⊆
        (univ.filter (fun m : L => p ∈ m)).image Sum.inr := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rcases y with p' | m
      · exact absurd hy incGraph_not_adj_inl_inl
      · simp only [mem_image, mem_filter, mem_univ, true_and]
        exact ⟨m, incGraph_adj_inl_inr.1 hy, rfl⟩
    refine (card_le_card this).trans (card_image_le.trans ?_)
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact (G.lines_on_pt p).le
  · have : univ.filter (fun y : P ⊕ L => (incGraph P L).Adj (.inr l) y) ⊆
        (univ.filter (fun p : P => p ∈ l)).image Sum.inl := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      rcases y with p | m
      · simp only [mem_image, mem_filter, mem_univ, true_and]
        exact ⟨p, incGraph_adj_inr_inl.1 hy, rfl⟩
      · exact absurd hy incGraph_not_adj_inr_inr
    refine (card_le_card this).trans (card_image_le.trans ?_)
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact (G.pts_on_line l).le

theorem card_vtx : Fintype.card (Vtx P L ι V U) =
    (Fintype.card P + Fintype.card L) * Fintype.card ι + Fintype.card V + Fintype.card U := by
  simp only [Vtx, Fintype.card_sum, Fintype.card_prod]
  ring

end Counting

/-- The colour class of a vertex: level vertices `A`-class iff `col x = τ i`, `𝓑`-hubs `false`, `𝓐`-hubs `true`. -/
def Data.vc (D : Data P L ι V U) : Vtx P L ι V U → Bool
  | .inl (x, i) => decide (col x = D.τ i)
  | .inr (.inl _) => false
  | .inr (.inr _) => true

namespace Hyp

variable {D : Data P L ι V U} (H : Hyp D)
include H

theorem vc_ne {a b : Vtx P L ι V U} (h : D.rel a b) : D.vc a ≠ D.vc b := by
  rcases a with ⟨x, i⟩ | v | u <;> rcases b with ⟨y, i'⟩ | v' | u'
  · rcases h with ⟨hxy, rfl⟩ | ⟨hT, hx, -, rfl⟩
    · have := col_adj_not hxy
      simp only [Data.vc]
      cases h1 : col x <;> cases h2 : col y <;> cases h3 : D.τ i <;> simp_all
    · have := H.maps i i' hT x hx
      simp only [Data.vc, hx, this]
      cases D.τ i' <;> simp
  · exact absurd h id
  · exact absurd h id
  · have h' : y = D.slotV v i' := h
    simp [Data.vc, h', H.slotA]
  · exact absurd h id
  · simp [Data.vc]
  · have h' : y = D.slotU u i' := h
    simp only [Data.vc, h', H.slotB]
    cases D.τ i' <;> simp
  · exact absurd h id
  · exact absurd h id

theorem colorable : D.X.Colorable 2 :=
  ⟨Coloring.mk (fun w => if D.vc w then (1 : Fin 2) else 0) fun {a b} h => by
    rcases (SimpleGraph.fromRel_adj _ _ _).1 h with ⟨-, h' | h'⟩
    · have := H.vc_ne h'
      cases h1 : D.vc a <;> cases h2 : D.vc b <;> simp_all
    · have := H.vc_ne h'
      cases h1 : D.vc a <;> cases h2 : D.vc b <;> simp_all⟩

end Hyp

section Degree

variable [Fintype P] [Fintype L] [Fintype ι] [Fintype V] [Fintype U]
variable {D : Data P L ι V U} {q r : ℕ} (H : Hyp D) (S : Surg D q r) (G : GQst P L q q)
include H S G

/-- In-degree of a regular tournament. -/
theorem Surg.indeg (i : ι) : (univ.filter (fun j => D.T j i)).card = r := by
  have h1 : (univ.filter (fun j => D.T j i)).card + (univ.filter (D.T i)).card + 1 = Fintype.card ι := by
    have : (univ : Finset ι) = (univ.filter (fun j => D.T j i)) ∪ (univ.filter (D.T i)) ∪ {i} := by
      ext j
      simp only [mem_univ, mem_union, mem_filter, true_and, mem_singleton, true_iff]
      by_cases h : j = i
      · exact Or.inr h
      · exact Or.inl ((H.total j i h).imp id id |>.symm.symm)
    have hd : Disjoint (univ.filter (fun j => D.T j i)) (univ.filter (D.T i)) := by
      rw [Finset.disjoint_left]
      intro j hj hj'
      simp only [mem_filter, mem_univ, true_and] at hj hj'
      exact S.anti i j hj' hj
    have hd2 : Disjoint ((univ.filter (fun j => D.T j i)) ∪ (univ.filter (D.T i))) {i} := by
      rw [disjoint_singleton_right]
      simp only [mem_union, mem_filter, mem_univ, true_and, not_or]
      exact ⟨fun h => H.irrefl _ _ h rfl, fun h => H.irrefl _ _ h rfl⟩
    have hc := congrArg Finset.card this
    rw [card_union_of_disjoint hd2, card_union_of_disjoint hd, card_singleton, card_univ] at hc
    omega
  have := S.outdeg i
  have := S.card_ι
  omega

/-- A vertex of the `A`-class of a level has at most `q + 1 + r` neighbours. -/
theorem Surg.deg_level_A {x : P ⊕ L} {i : ι} (hx : col x = D.τ i) :
    (D.X.neighborSet (.inl (x, i))).ncard ≤ q + 1 + r := by
  let F : Finset (Vtx P L ι V U) :=
    ((univ.filter (fun y => (incGraph P L).Adj x y)).image (fun y => (.inl (y, i) : Vtx P L ι V U))) ∪
    ((univ.filter (fun j => D.T i j ∧ x ∉ D.R i j)).image (fun j => (.inl (D.M i j x, j) : Vtx P L ι V U))) ∪
    ((univ.filter (fun v => D.slotV v i = x)).image (fun v => (.inr (.inl v) : Vtx P L ι V U)))
  have hsub : D.X.neighborSet (.inl (x, i)) ⊆ ↑F := by
    intro z hz
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hz with ⟨-, h | h⟩
    · rcases z with ⟨y, i'⟩ | v | u
      · rcases h with ⟨hxy, rfl⟩ | ⟨hT, -, hR, rfl⟩
        · exact mem_coe.2 (mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, mem_filter.2 ⟨mem_univ _, hxy⟩, rfl⟩)))
        · exact mem_coe.2 (mem_union_left _ (mem_union_right _ (mem_image.2 ⟨i', mem_filter.2 ⟨mem_univ _, hT, hR⟩, rfl⟩)))
      · exact absurd h id
      · exact absurd h id
    · rcases z with ⟨y, i'⟩ | v | u
      · rcases h with ⟨hxy, rfl⟩ | ⟨hT, hy, hR, hxy⟩
        · exact mem_coe.2 (mem_union_left _ (mem_union_left _ (mem_image.2 ⟨y, mem_filter.2 ⟨mem_univ _, hxy.symm⟩, rfl⟩)))
        · have := H.maps i' i hT y hy
          rw [← hxy, hx] at this
          exfalso; generalize D.τ i = b at this; cases b <;> simp at this
      · have h' : x = D.slotV v i := h
        exact mem_coe.2 (mem_union_right _ (mem_image.2 ⟨v, mem_filter.2 ⟨mem_univ _, h'.symm⟩, rfl⟩))
      · have h' : x = D.slotU u i := h
        have := H.slotB u i
        rw [← h', hx] at this
        exfalso; generalize D.τ i = b at this; cases b <;> simp at this
  have hcard : F.card ≤ q + 1 + r := by
    have hA := card_nbr_le G x
    have hB : (univ.filter (fun j => D.T i j ∧ x ∉ D.R i j)).card +
        (univ.filter (fun j => D.T i j ∧ x ∈ D.R i j)).card = r := by
      rw [← S.outdeg i, ← card_union_of_disjoint]
      · congr 1; ext j; simp only [mem_union, mem_filter, mem_univ, true_and]; tauto
      · rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_filter, mem_univ, true_and] at h1 h2; exact h1.2 h2.2
    have hC : (univ.filter (fun v => D.slotV v i = x)).card ≤
        (univ.filter (fun j => D.T i j ∧ x ∈ D.R i j)).card := by
      refine card_le_card_of_injOn (fun v => S.arcV v i) ?_ ?_
      · intro v hv
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv ⊢
        exact ⟨S.arcV_T v i, hv ▸ S.arcV_R v i⟩
      · intro v hv v' hv' he
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv hv'
        exact S.arcV_inj v v' i (hv.trans hv'.symm) he
    have h1 : F.card ≤ (univ.filter (fun y => (incGraph P L).Adj x y)).card +
        (univ.filter (fun j => D.T i j ∧ x ∉ D.R i j)).card + (univ.filter (fun v => D.slotV v i = x)).card :=
      (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
        (Nat.add_le_add card_image_le card_image_le)) card_image_le)
    omega
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans (by rw [Set.ncard_coe_finset]; exact hcard)

/-- A vertex of the `B`-class of a level has at most `q + 1 + r` neighbours. -/
theorem Surg.deg_level_B {x : P ⊕ L} {i : ι} (hx : col x = !D.τ i) :
    (D.X.neighborSet (.inl (x, i))).ncard ≤ q + 1 + r := by
  let F : Finset (Vtx P L ι V U) :=
    ((univ.filter (fun y => (incGraph P L).Adj x y)).image (fun y => (.inl (y, i) : Vtx P L ι V U))) ∪
    ((univ.filter (fun j => D.T j i ∧ (D.M j i).symm x ∉ D.R j i)).image
      (fun j => (.inl ((D.M j i).symm x, j) : Vtx P L ι V U))) ∪
    ((univ.filter (fun u => D.slotU u i = x)).image (fun u => (.inr (.inr u) : Vtx P L ι V U)))
  have hsub : D.X.neighborSet (.inl (x, i)) ⊆ ↑F := by
    intro z hz
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hz with ⟨-, h | h⟩
    · rcases z with ⟨y, i'⟩ | v | u
      · rcases h with ⟨hxy, rfl⟩ | ⟨hT, hy, hR, hxy⟩
        · exact mem_coe.2 (mem_union_left _ (mem_union_left _
            (mem_image.2 ⟨y, mem_filter.2 ⟨mem_univ _, hxy⟩, rfl⟩)))
        · have := H.maps i i' hT x hy
          rw [hx] at hy
          exfalso; generalize D.τ i = b at hy; cases b <;> simp at hy
      · exact absurd h id
      · exact absurd h id
    · rcases z with ⟨y, i'⟩ | v | u
      · rcases h with ⟨hxy, rfl⟩ | ⟨hT, hy, hR, hxy⟩
        · exact mem_coe.2 (mem_union_left _ (mem_union_left _
            (mem_image.2 ⟨y, mem_filter.2 ⟨mem_univ _, hxy.symm⟩, rfl⟩)))
        · have hy' : y = (D.M i' i).symm x := by rw [hxy]; simp
          subst hy'
          exact mem_coe.2 (mem_union_left _ (mem_union_right _
            (mem_image.2 ⟨i', mem_filter.2 ⟨mem_univ _, hT, hR⟩, rfl⟩)))
      · have h' : x = D.slotV v i := h
        have := H.slotA v i
        rw [← h', hx] at this
        exfalso; generalize D.τ i = b at this; cases b <;> simp at this
      · have h' : x = D.slotU u i := h
        exact mem_coe.2 (mem_union_right _ (mem_image.2 ⟨u, mem_filter.2 ⟨mem_univ _, h'.symm⟩, rfl⟩))
  have hcard : F.card ≤ q + 1 + r := by
    have hA := card_nbr_le G x
    have hB : (univ.filter (fun j => D.T j i ∧ (D.M j i).symm x ∉ D.R j i)).card +
        (univ.filter (fun j => D.T j i ∧ (D.M j i).symm x ∈ D.R j i)).card = r := by
      rw [← S.indeg H G i, ← card_union_of_disjoint]
      · congr 1; ext j; simp only [mem_union, mem_filter, mem_univ, true_and]; tauto
      · rw [Finset.disjoint_left]; intro j h1 h2; simp only [mem_filter, mem_univ, true_and] at h1 h2; exact h1.2 h2.2
    have hC : (univ.filter (fun u => D.slotU u i = x)).card ≤
        (univ.filter (fun j => D.T j i ∧ (D.M j i).symm x ∈ D.R j i)).card := by
      refine card_le_card_of_injOn (fun u => S.arcU u i) ?_ ?_
      · intro u hu
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu ⊢
        exact ⟨S.arcU_T u i, hu ▸ S.arcU_R u i⟩
      · intro u hu u' hu' he
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hu hu'
        exact S.arcU_inj u u' i (hu.trans hu'.symm) he
    have h1 : F.card ≤ (univ.filter (fun y => (incGraph P L).Adj x y)).card +
        (univ.filter (fun j => D.T j i ∧ (D.M j i).symm x ∉ D.R j i)).card +
        (univ.filter (fun u => D.slotU u i = x)).card :=
      (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
        (Nat.add_le_add card_image_le card_image_le)) card_image_le)
    omega
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans (by rw [Set.ncard_coe_finset]; exact hcard)

/-- A `𝓑`-hub has at most `q + 1 + r` neighbours. -/
theorem Surg.deg_hubV (v : V) : (D.X.neighborSet (.inr (.inl v))).ncard ≤ q + 1 + r := by
  let F : Finset (Vtx P L ι V U) :=
    (univ.image (fun i => (.inl (D.slotV v i, i) : Vtx P L ι V U))) ∪
    ((univ.filter (D.NS v)).image (fun u => (.inr (.inr u) : Vtx P L ι V U)))
  have hsub : D.X.neighborSet (.inr (.inl v)) ⊆ ↑F := by
    intro z hz
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hz with ⟨-, h | h⟩
    · rcases z with ⟨y, i'⟩ | v' | u
      · have h' : y = D.slotV v i' := h
        exact mem_coe.2 (mem_union_left _ (mem_image.2 ⟨i', mem_univ _, by rw [h']⟩))
      · exact absurd h id
      · exact mem_coe.2 (mem_union_right _ (mem_image.2 ⟨u, mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩))
    · rcases z with ⟨y, i'⟩ | v' | u
      · exact absurd h id
      · exact absurd h id
      · exact absurd h id
  have hcard : F.card ≤ q + 1 + r := by
    have h1 : F.card ≤ (univ : Finset ι).card + (univ.filter (D.NS v)).card :=
      (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
    have := S.hubV v
    rw [card_univ, S.card_ι] at h1
    omega
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans (by rw [Set.ncard_coe_finset]; exact hcard)

/-- An `𝓐`-hub has at most `q + 1 + r` neighbours. -/
theorem Surg.deg_hubU (u : U) : (D.X.neighborSet (.inr (.inr u))).ncard ≤ q + 1 + r := by
  let F : Finset (Vtx P L ι V U) :=
    (univ.image (fun i => (.inl (D.slotU u i, i) : Vtx P L ι V U))) ∪
    ((univ.filter (fun v => D.NS v u)).image (fun v => (.inr (.inl v) : Vtx P L ι V U)))
  have hsub : D.X.neighborSet (.inr (.inr u)) ⊆ ↑F := by
    intro z hz
    rcases (SimpleGraph.fromRel_adj _ _ _).1 hz with ⟨-, h | h⟩
    · rcases z with ⟨y, i'⟩ | v' | u'
      · have h' : y = D.slotU u i' := h
        exact mem_coe.2 (mem_union_left _ (mem_image.2 ⟨i', mem_univ _, by rw [h']⟩))
      · exact absurd h id
      · exact absurd h id
    · rcases z with ⟨y, i'⟩ | v' | u'
      · exact absurd h id
      · exact mem_coe.2 (mem_union_right _ (mem_image.2 ⟨v', mem_filter.2 ⟨mem_univ _, h⟩, rfl⟩))
      · exact absurd h id
  have hcard : F.card ≤ q + 1 + r := by
    have h1 : F.card ≤ (univ : Finset ι).card + (univ.filter (fun v => D.NS v u)).card :=
      (card_union_le _ _).trans (Nat.add_le_add card_image_le card_image_le)
    have := S.hubU u
    rw [card_univ, S.card_ι] at h1
    omega
  exact (Set.ncard_le_ncard hsub (Finset.finite_toSet F)).trans (by rw [Set.ncard_coe_finset]; exact hcard)

/-- Every vertex of `X_R^+` has at most `q + 1 + r` neighbours. -/
theorem Surg.degree_le (w : Vtx P L ι V U) : (D.X.neighborSet w).ncard ≤ q + 1 + r := by
  rcases w with ⟨x, i⟩ | v | u
  · by_cases hx : col x = D.τ i
    · exact S.deg_level_A H G hx
    · exact S.deg_level_B H G (by cases h1 : col x <;> cases h2 : D.τ i <;> simp_all)
  · exact S.deg_hubV H G v
  · exact S.deg_hubU H G u

end Degree

end BipartiteDD.LeanMaxx.D5
