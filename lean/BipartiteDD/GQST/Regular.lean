import BipartiteDD.GQST.Main
import BipartiteDD.GQST.Biregular
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-! Group GQST, part 7: the copy graph made `Δ`-regular.

Step 1 (`ediam_le_of_le`, `colorable_of_add_edges`): adding edges does not increase the extended diameter,
and keeps 2-colourability when the new edges join the two colour classes.

Step 2 (`regular_copy_graph`): let `G` be a generalized quadrangle of order `(s, t)`, `w` an exact weighted
`(Δ − s − 1)`-ovoid (every line carries total point weight `Δ − s − 1`) and `m` an exact `(Δ − t − 1)`-cover
(every point carries total line weight `Δ − t − 1`). Then the weighted copy graph plus a biregular bipartite
graph between point copies and line copies is `Δ`-regular, bipartite, and of diameter at most `4`.

The biregular graph is `biRel` of `GQST.Biregular`: each point copy gets `Δ − t − 1` new partners among the
line copies and each line copy gets `Δ − s − 1` new partners among the point copies. The counts agree because
of double counting of the flags of the quadrangle (`card_biregular_identity`). Originals already have
degree `Δ`, and no edge is added at an original vertex. -/

namespace BipartiteDD

open SimpleGraph

/-! ### Step 1: adding edges -/

section AddEdges

variable {V : Type*}

/-- Adding edges does not increase the extended diameter. -/
theorem ediam_le_of_le {G H : SimpleGraph V} (h : G ≤ H) {D : ℕ∞} (hG : G.ediam ≤ D) :
    H.ediam ≤ D :=
  ediam_le_iff.2 fun _ _ => (edist_anti h).trans (edist_le_ediam.trans hG)

/-- Adding edges keeps the graph 2-colourable when the colouring `c` of `G` is proper and every new edge
joins two vertices of different colours. -/
theorem colorable_of_add_edges {G H : SimpleGraph V} (c : V → Fin 2)
    (hG : ∀ {u v}, G.Adj u v → c u ≠ c v) (hH : ∀ {u v}, H.Adj u v → G.Adj u v ∨ c u ≠ c v) :
    H.Colorable 2 :=
  ⟨SimpleGraph.Coloring.mk c fun h => (hH h).elim (fun h' => hG h') id⟩

end AddEdges

end BipartiteDD

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- Vertices of the weighted copy graph, as in `blowup`. -/
abbrev Vtx (P L : Type*) [Membership P L] (w : P → ℕ) (m : L → ℕ) :=
  (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))

variable {w : P → ℕ} {m : L → ℕ}

/-- The extra edges: a point copy `x` is joined to a line copy `y` exactly when `R x y`. -/
def extraAdj (R : (Σ p, Fin (w p)) → (Σ l, Fin (m l)) → Prop) (u v : Vtx P L w m) : Prop :=
  ∃ x y, R x y ∧ ((u = .inl (.inr x) ∧ v = .inr (.inr y)) ∨ (u = .inr (.inr y) ∧ v = .inl (.inr x)))

/-- The copy graph of `blowup`, with the biregular extra edges added. -/
def regGraph (R : (Σ p, Fin (w p)) → (Σ l, Fin (m l)) → Prop) : SimpleGraph (Vtx P L w m) where
  Adj u v := (blowup P L w m).Adj u v ∨ extraAdj R u v
  symm := ⟨fun u v h => by
    rcases h with h | ⟨x, y, hR, h | h⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨x, y, hR, Or.inr h.symm⟩
    · exact Or.inr ⟨x, y, hR, Or.inl h.symm⟩⟩
  loopless := ⟨fun u h => by
    rcases h with h | ⟨x, y, -, h | h⟩
    · exact (blowup P L w m).irrefl h
    · cases h.1.symm.trans h.2
    · cases h.1.symm.trans h.2⟩

variable (R : (Σ p, Fin (w p)) → (Σ l, Fin (m l)) → Prop)

theorem regGraph_adj_iff (u v : Vtx P L w m) :
    (regGraph R).Adj u v ↔ (blowup P L w m).Adj u v ∨ extraAdj R u v :=
  Iff.rfl

theorem extraAdj_pt_iff (x : Σ p, Fin (w p)) (u : Vtx P L w m) :
    extraAdj R (.inl (.inr x)) u ↔ ∃ y, u = .inr (.inr y) ∧ R x y := by
  constructor
  · rintro ⟨x', y, hR, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · cases h1
      exact ⟨y, h2, hR⟩
    · cases h1
  · rintro ⟨y, rfl, hR⟩
    exact ⟨x, y, hR, Or.inl ⟨rfl, rfl⟩⟩

theorem extraAdj_line_iff (y : Σ l, Fin (m l)) (u : Vtx P L w m) :
    extraAdj R (.inr (.inr y)) u ↔ ∃ x, u = .inl (.inr x) ∧ R x y := by
  constructor
  · rintro ⟨x', y', hR, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · cases h1
    · cases h1
      exact ⟨x', h2, hR⟩
  · rintro ⟨x, rfl, hR⟩
    exact ⟨x, y, hR, Or.inr ⟨rfl, rfl⟩⟩

/-! ### Neighbourhoods are ranges of explicit maps -/

/-- Neighbourhood of an original point `p`: the lines through `p`, and the copies of those lines
through `p`. -/
theorem nbr_orig_pt (p : P) :
    (regGraph R).neighborSet (.inl (.inl p)) =
      Set.range (Sum.elim
        (fun l : {l : L // p ∈ l} => (.inr (.inl l.1) : Vtx P L w m))
        (fun z : (Σ l : {l : L // p ∈ l}, Fin (m l.1)) =>
          (.inr (.inr ⟨z.1.1, z.2⟩) : Vtx P L w m))) := by
  ext u
  rw [mem_neighborSet, Set.mem_range]
  constructor
  · intro hu
    rw [regGraph_adj_iff] at hu
    rcases hu with hb | he
    · rw [blowup_adj_iff] at hb
      rcases u with (q | x) | (l | y)
      · exact (incGraph_not_adj_inl_inl hb.1).elim
      · exact (incGraph_not_adj_inl_inl hb.1).elim
      · exact ⟨Sum.inl ⟨l, incGraph_adj_inl_inr.1 hb.1⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨y.1, incGraph_adj_inl_inr.1 hb.1⟩, y.2⟩, rfl⟩
    · obtain ⟨x, y, -, ⟨h, -⟩ | ⟨h, -⟩⟩ := he <;> cases h
  · rintro ⟨z, rfl⟩
    rcases z with l | ⟨⟨l, hl⟩, k⟩
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inl_inr.2 l.2, Or.inl trivial⟩
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inl_inr.2 hl, Or.inl trivial⟩

/-- Neighbourhood of an original line `l`: the points on `l`, and the copies of points on `l`. -/
theorem nbr_orig_line (l : L) :
    (regGraph R).neighborSet (.inr (.inl l)) =
      Set.range (Sum.elim
        (fun p : {p : P // p ∈ l} => (.inl (.inl p.1) : Vtx P L w m))
        (fun z : (Σ x : {x : P // x ∈ l}, Fin (w x.1)) =>
          (.inl (.inr ⟨z.1.1, z.2⟩) : Vtx P L w m))) := by
  ext u
  rw [mem_neighborSet, Set.mem_range]
  constructor
  · intro hu
    rw [regGraph_adj_iff] at hu
    rcases hu with hb | he
    · rw [blowup_adj_iff] at hb
      rcases u with (q | x) | (l' | y)
      · exact ⟨Sum.inl ⟨q, incGraph_adj_inr_inl.1 hb.1⟩, rfl⟩
      · exact ⟨Sum.inr ⟨⟨x.1, incGraph_adj_inr_inl.1 hb.1⟩, x.2⟩, rfl⟩
      · exact (incGraph_not_adj_inr_inr hb.1).elim
      · exact (incGraph_not_adj_inr_inr hb.1).elim
    · obtain ⟨x, y, -, ⟨h, -⟩ | ⟨h, -⟩⟩ := he <;> cases h
  · rintro ⟨z, rfl⟩
    rcases z with p | ⟨⟨x, hx⟩, i⟩
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inr_inl.2 p.2, Or.inl trivial⟩
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inr_inl.2 hx, Or.inl trivial⟩

/-- Neighbourhood of a point copy `x`: the lines through `x.1`, and the line copies `y` with `R x y`. -/
theorem nbr_pt_copy (x : Σ p, Fin (w p)) :
    (regGraph R).neighborSet (.inl (.inr x)) =
      Set.range (Sum.elim
        (fun l : {l : L // x.1 ∈ l} => (.inr (.inl l.1) : Vtx P L w m))
        (fun y : {y : Σ l, Fin (m l) // R x y} => (.inr (.inr y.1) : Vtx P L w m))) := by
  ext u
  rw [mem_neighborSet, Set.mem_range]
  constructor
  · intro hu
    rw [regGraph_adj_iff] at hu
    rcases hu with hb | he
    · rw [blowup_adj_iff] at hb
      rcases u with (q | x') | (l | y)
      · exact (incGraph_not_adj_inl_inl hb.1).elim
      · exact (incGraph_not_adj_inl_inl hb.1).elim
      · exact ⟨Sum.inl ⟨l, incGraph_adj_inl_inr.1 hb.1⟩, rfl⟩
      · exact (hb.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
    · obtain ⟨y, rfl, hR⟩ := (extraAdj_pt_iff R x _).1 he
      exact ⟨Sum.inr ⟨y, hR⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    rcases z with l | y
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inl_inr.2 l.2, Or.inr trivial⟩
    · exact (regGraph_adj_iff R _ _).2 (Or.inr ((extraAdj_pt_iff R x _).2 ⟨y.1, rfl, y.2⟩))

/-- Neighbourhood of a line copy `y`: the points on `y.1`, and the point copies `x` with `R x y`. -/
theorem nbr_line_copy (y : Σ l, Fin (m l)) :
    (regGraph R).neighborSet (.inr (.inr y)) =
      Set.range (Sum.elim
        (fun p : {p : P // p ∈ y.1} => (.inl (.inl p.1) : Vtx P L w m))
        (fun x : {x : Σ p, Fin (w p) // R x y} => (.inl (.inr x.1) : Vtx P L w m))) := by
  ext u
  rw [mem_neighborSet, Set.mem_range]
  constructor
  · intro hu
    rw [regGraph_adj_iff] at hu
    rcases hu with hb | he
    · rw [blowup_adj_iff] at hb
      rcases u with (q | x') | (l' | y')
      · exact ⟨Sum.inl ⟨q, incGraph_adj_inr_inl.1 hb.1⟩, rfl⟩
      · exact (hb.2.elim (fun h => by simp [isOrig] at h) (fun h => by simp [isOrig] at h))
      · exact (incGraph_not_adj_inr_inr hb.1).elim
      · exact (incGraph_not_adj_inr_inr hb.1).elim
    · obtain ⟨x, rfl, hR⟩ := (extraAdj_line_iff R y _).1 he
      exact ⟨Sum.inr ⟨x, hR⟩, rfl⟩
  · rintro ⟨z, rfl⟩
    rcases z with p | x
    · refine (regGraph_adj_iff R _ _).2 (Or.inl ?_)
      rw [blowup_adj_iff]
      exact ⟨incGraph_adj_inr_inl.2 p.2, Or.inr trivial⟩
    · exact (regGraph_adj_iff R _ _).2 (Or.inr ((extraAdj_line_iff R y _).2 ⟨x.1, rfl, x.2⟩))

/-! ### Cardinalities of the neighbourhoods -/

theorem sum_filter_mem {α : Type*} [Fintype α] (q : α → Prop) [DecidablePred q] (f : α → ℕ) :
    ∑ x : {x // q x}, f x.1 = ∑ x ∈ Finset.univ.filter q, f x :=
  (Finset.sum_subtype (Finset.univ.filter q) (by simp) f).symm

theorem injective_sum_elim {α β γ : Type*} {f : α → γ} {g : β → γ} (hf : Function.Injective f)
    (hg : Function.Injective g) (hd : ∀ a b, f a ≠ g b) : Function.Injective (Sum.elim f g) := by
  rintro (a | a) (b | b) h
  · exact congrArg Sum.inl (hf h)
  · exact absurd h (hd a b)
  · exact absurd h.symm (hd b a)
  · exact congrArg Sum.inr (hg h)

theorem ncard_range_sum_elim {α β γ : Type*} [Finite α] [Finite β] {f : α → γ} {g : β → γ}
    (hf : Function.Injective f) (hg : Function.Injective g) (hd : ∀ a b, f a ≠ g b) :
    (Set.range (Sum.elim f g)).ncard = Nat.card α + Nat.card β := by
  rw [Set.ncard_range_of_injective (injective_sum_elim hf hg hd), Nat.card_sum]

theorem sigma_sub_inj {α : Type*} {q : α → Prop} {n : α → ℕ} (z z' : Σ l : {l // q l}, Fin (n l.1))
    (h : (⟨z.1.1, z.2⟩ : Σ a, Fin (n a)) = ⟨z'.1.1, z'.2⟩) : z = z' := by
  obtain ⟨⟨l, hl⟩, k⟩ := z
  obtain ⟨⟨l', hl'⟩, k'⟩ := z'
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  subst h1
  obtain rfl := eq_of_heq h2
  rfl

variable [Fintype P] [Fintype L] {s t : ℕ}

/-- The number of neighbours of an original point `p` is `t + 1` plus the total line weight through `p`. -/
theorem card_nbr_orig_pt (G : GQst P L s t) (p : P) :
    ((regGraph R).neighborSet (.inl (.inl p))).ncard =
      t + 1 + ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l := by
  have hc : Nat.card (Σ l : {l : L // p ∈ l}, Fin (m l.1)) =
      ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l := by
    rw [Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact sum_filter_mem (fun l : L => p ∈ l) m
  rw [nbr_orig_pt R p, ncard_range_sum_elim
    (fun a b h => Subtype.ext (Sum.inl.inj (Sum.inr.inj h)))
    (fun a b h => sigma_sub_inj a b (Sum.inr.inj (Sum.inr.inj h)))
    (fun _ _ h => by cases h), hc, G.lines_on_pt p]

/-- The number of neighbours of an original line `l` is `s + 1` plus the total point weight on `l`. -/
theorem card_nbr_orig_line (G : GQst P L s t) (l : L) :
    ((regGraph R).neighborSet (.inr (.inl l))).ncard =
      s + 1 + ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x := by
  have hc : Nat.card (Σ x : {x : P // x ∈ l}, Fin (w x.1)) =
      ∑ x ∈ Finset.univ.filter (fun x => x ∈ l), w x := by
    rw [Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact sum_filter_mem (fun x => x ∈ l) w
  rw [nbr_orig_line R l, ncard_range_sum_elim
    (fun a b h => Subtype.ext (Sum.inl.inj (Sum.inl.inj h)))
    (fun a b h => sigma_sub_inj a b (Sum.inr.inj (Sum.inl.inj h)))
    (fun _ _ h => by cases h), hc, G.pts_on_line l]

/-- The number of neighbours of a point copy `x` is `t + 1` plus the number of line copies joined to `x`. -/
theorem card_nbr_pt_copy (G : GQst P L s t) (x : Σ p, Fin (w p)) :
    ((regGraph R).neighborSet (.inl (.inr x))).ncard =
      t + 1 + Nat.card {y : Σ l, Fin (m l) // R x y} := by
  rw [nbr_pt_copy R x, ncard_range_sum_elim
    (fun a b h => Subtype.ext (Sum.inl.inj (Sum.inr.inj h)))
    (fun a b h => Subtype.ext (Sum.inr.inj (Sum.inr.inj h)))
    (fun _ _ h => by cases h), G.lines_on_pt x.1]

/-- The number of neighbours of a line copy `y` is `s + 1` plus the number of point copies joined to `y`. -/
theorem card_nbr_line_copy (G : GQst P L s t) (y : Σ l, Fin (m l)) :
    ((regGraph R).neighborSet (.inr (.inr y))).ncard =
      s + 1 + Nat.card {x : Σ p, Fin (w p) // R x y} := by
  rw [nbr_line_copy R y, ncard_range_sum_elim
    (fun a b h => Subtype.ext (Sum.inl.inj (Sum.inl.inj h)))
    (fun a b h => Subtype.ext (Sum.inr.inj (Sum.inl.inj h)))
    (fun _ _ h => by cases h), G.pts_on_line y.1]

/-! ### The counting identity and the biregular graph -/

/-- Double counting of the flags of the quadrangle. -/
theorem card_biregular_identity (G : GQst P L s t) (Δ : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p = Δ - (s + 1))
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l = Δ - (t + 1)) :
    (∑ p, w p) * (Δ - (t + 1)) = (∑ l, m l) * (Δ - (s + 1)) := by
  have hpl : ∀ p : P, (Finset.univ.filter (fun l : L => p ∈ l)).card = t + 1 := fun p => by
    have := G.lines_on_pt p
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact this
  have hlp : ∀ l : L, (Finset.univ.filter (fun p : P => p ∈ l)).card = s + 1 := fun l => by
    have := G.pts_on_line l
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
    exact this
  have key1 : ∑ l : L, ∑ p ∈ Finset.univ.filter (fun p : P => p ∈ l), w p =
      ∑ p : P, (Finset.univ.filter (fun l : L => p ∈ l)).card * w p := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have key2 : ∑ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l =
      ∑ l : L, (Finset.univ.filter (fun p : P => p ∈ l)).card * m l := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
  have E1 : (t + 1) * ∑ p, w p = Fintype.card L * (Δ - (s + 1)) := by
    calc (t + 1) * ∑ p, w p = ∑ p : P, (t + 1) * w p := by rw [Finset.mul_sum]
      _ = ∑ p : P, (Finset.univ.filter (fun l : L => p ∈ l)).card * w p :=
          Finset.sum_congr rfl fun p _ => by rw [hpl p]
      _ = ∑ l : L, ∑ p ∈ Finset.univ.filter (fun p : P => p ∈ l), w p := key1.symm
      _ = ∑ l : L, (Δ - (s + 1)) := Finset.sum_congr rfl fun l _ => hw l
      _ = Fintype.card L * (Δ - (s + 1)) := by simp
  have E2 : (s + 1) * ∑ l, m l = Fintype.card P * (Δ - (t + 1)) := by
    calc (s + 1) * ∑ l, m l = ∑ l : L, (s + 1) * m l := by rw [Finset.mul_sum]
      _ = ∑ l : L, (Finset.univ.filter (fun p : P => p ∈ l)).card * m l :=
          Finset.sum_congr rfl fun l _ => by rw [hlp l]
      _ = ∑ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l := key2.symm
      _ = ∑ p : P, (Δ - (t + 1)) := Finset.sum_congr rfl fun p _ => hm p
      _ = Fintype.card P * (Δ - (t + 1)) := by simp
  have E3 : (s + 1) * Fintype.card L = (t + 1) * Fintype.card P := by
    have k : ∑ l : L, (Finset.univ.filter (fun p : P => p ∈ l)).card =
        ∑ p : P, (Finset.univ.filter (fun l : L => p ∈ l)).card := by
      simp only [Finset.card_filter]
      exact Finset.sum_comm
    simp only [hpl, hlp, Finset.sum_const, Finset.card_univ, smul_eq_mul] at k
    rw [mul_comm (s + 1), mul_comm (t + 1)]
    exact k
  have K : ((t + 1) * (s + 1)) * ((∑ p, w p) * (Δ - (t + 1))) =
      ((t + 1) * (s + 1)) * ((∑ l, m l) * (Δ - (s + 1))) := by
    calc ((t + 1) * (s + 1)) * ((∑ p, w p) * (Δ - (t + 1)))
        = (s + 1) * (Δ - (t + 1)) * ((t + 1) * ∑ p, w p) := by ring
      _ = (s + 1) * (Δ - (t + 1)) * (Fintype.card L * (Δ - (s + 1))) := by rw [E1]
      _ = ((s + 1) * Fintype.card L) * ((Δ - (t + 1)) * (Δ - (s + 1))) := by ring
      _ = ((t + 1) * Fintype.card P) * ((Δ - (t + 1)) * (Δ - (s + 1))) := by rw [E3]
      _ = (t + 1) * (Δ - (s + 1)) * (Fintype.card P * (Δ - (t + 1))) := by ring
      _ = (t + 1) * (Δ - (s + 1)) * ((s + 1) * ∑ l, m l) := by rw [E2]
      _ = ((t + 1) * (s + 1)) * ((∑ l, m l) * (Δ - (s + 1))) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) K

/-- The biregular relation between point copies and line copies. -/
theorem exists_biregular_copies (G : GQst P L s t) (Δ : ℕ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p = Δ - (s + 1))
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l = Δ - (t + 1)) :
    ∃ R : (Σ p, Fin (w p)) → (Σ l, Fin (m l)) → Prop,
      (∀ x, Nat.card {y // R x y} = Δ - (t + 1)) ∧ (∀ y, Nat.card {x // R x y} = Δ - (s + 1)) := by
  have hid := card_biregular_identity G Δ hw hm
  have hsum_w : Fintype.card (Σ p, Fin (w p)) = ∑ p, w p := by simp [Fintype.card_sigma]
  have hsum_m : Fintype.card (Σ l, Fin (m l)) = ∑ l, m l := by simp [Fintype.card_sigma]
  have hab : Fintype.card (Σ p, Fin (w p)) * (Δ - (t + 1)) =
      Fintype.card (Σ l, Fin (m l)) * (Δ - (s + 1)) := by
    rw [hsum_w, hsum_m]
    exact hid
  have hA : 0 < Fintype.card (Σ p, Fin (w p)) → Δ - (t + 1) ≤ Fintype.card (Σ l, Fin (m l)) := by
    intro ha
    obtain ⟨x⟩ := Fintype.card_pos_iff.1 ha
    rw [hsum_m, ← hm x.1]
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  obtain ⟨R', h1, h2⟩ := biregular_exists _ _ _ _ hab hA
  refine ⟨fun x y => R' (Fintype.equivFin (Σ p, Fin (w p)) x)
    (Fintype.equivFin (Σ l, Fin (m l)) y), fun x => ?_, fun y => ?_⟩
  · exact (Nat.card_congr (Equiv.subtypeEquiv (Fintype.equivFin (Σ l, Fin (m l)))
      fun y => Iff.rfl)).trans (h1 _)
  · exact (Nat.card_congr (Equiv.subtypeEquiv (Fintype.equivFin (Σ p, Fin (w p)))
      fun x => Iff.rfl)).trans (h2 _)

/-! ### The main theorem -/

/-- The colour of a vertex of the copy graph: the point side is colour `0`, the line side colour `1`. -/
def colourOf (v : Vtx P L w m) : Fin 2 :=
  if (under (w := w) (m := m) v).isLeft then 0 else 1

/-- Group GQST, regular version. For a generalized quadrangle `G` of order `(s, t)`, an exact weighted
`(Δ − s − 1)`-ovoid `w` and an exact `(Δ − t − 1)`-cover `m`, there is a `Δ`-regular bipartite graph of
diameter at most `4` on the vertices of the weighted copy graph. -/
theorem regular_copy_graph (G : GQst P L s t) (Δ : ℕ) (hs : s + 1 ≤ Δ) (ht : t + 1 ≤ Δ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), w p = Δ - (s + 1))
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l = Δ - (t + 1)) :
    ∃ H : SimpleGraph (Vtx P L w m), H.Colorable 2 ∧ (∀ v, (H.neighborSet v).ncard = Δ) ∧
      H.ediam ≤ 4 := by
  obtain ⟨R, hR1, hR2⟩ := exists_biregular_copies G Δ hw hm
  refine ⟨regGraph R, ?_, ?_, ?_⟩
  · refine colorable_of_add_edges (G := blowup P L w m) colourOf ?_ ?_
    · intro u v h
      have hne := incGraph_isLeft_ne (blowup_adj_iff.1 h).1
      unfold colourOf
      cases hu : (under (w := w) (m := m) u).isLeft <;>
        cases hv : (under (w := w) (m := m) v).isLeft <;> simp_all
    · intro u v h
      rw [regGraph_adj_iff] at h
      rcases h with h | ⟨x, y, -, h | h⟩
      · exact Or.inl h
      · obtain ⟨h1, h2⟩ := h
        subst h1 h2
        exact Or.inr (by simp [colourOf, under])
      · obtain ⟨h1, h2⟩ := h
        subst h1 h2
        exact Or.inr (by simp [colourOf, under])
  · intro v
    rcases v with (p | x) | (l | y)
    · rw [card_nbr_orig_pt R G p, hm p]
      omega
    · rw [card_nbr_pt_copy R G x, hR1 x]
      omega
    · rw [card_nbr_orig_line R G l, hw l]
      omega
    · rw [card_nbr_line_copy R G y, hR2 y]
      omega
  · exact ediam_le_of_le (fun _ _ h => Or.inl h) (blowup_ediam G w m)

/-- Transport along a bijection: a `Δ`-regular bipartite graph of diameter at most `D` stays so. -/
theorem regular_comap {V V' : Type*} (e : V ≃ V') (H : SimpleGraph V) (Δ : ℕ) {D : ℕ∞}
    (hc : H.Colorable 2) (hd : ∀ v, (H.neighborSet v).ncard = Δ) (he : H.ediam ≤ D) :
    (H.comap e.symm).Colorable 2 ∧ (∀ v, ((H.comap e.symm).neighborSet v).ncard = Δ) ∧
      (H.comap e.symm).ediam ≤ D := by
  refine ⟨Colorable.of_hom (SimpleGraph.Iso.comap e.symm H).toHom hc, fun v => ?_, ?_⟩
  · have hset : (H.comap e.symm).neighborSet v = e.symm ⁻¹' (H.neighborSet (e.symm v)) := by
      ext w
      exact Iff.rfl
    rw [hset, Set.ncard_preimage_of_injective_subset_range e.symm.injective
      (by rw [e.symm.surjective.range_eq]; exact Set.subset_univ _)]
    exact hd _
  · rw [ediam_le_iff]
    intro u v
    have h := edist_le_of_hom (comapHom e H) (e.symm u) (e.symm v)
    have hu : comapHom e H (e.symm u) = u := e.apply_symm_apply u
    have hv : comapHom e H (e.symm v) = v := e.apply_symm_apply v
    rw [hu, hv] at h
    exact h.trans (edist_le_ediam.trans he)

/-- Group GQST, regular version on `Fin n`. The number of vertices is
`|P| + |L| + ∑ w + ∑ m`, as for `GQST.gqst`. -/
theorem regular_copy_graph_fin {s t : ℕ} (G : GQst P L s t) (Δ : ℕ)
    (hs : s + 1 ≤ Δ) (ht : t + 1 ≤ Δ)
    (hw : ∀ l : L, ∑ p ∈ Finset.univ.filter (fun p : P => p ∈ l), w p = Δ - (s + 1))
    (hm : ∀ p : P, ∑ l ∈ Finset.univ.filter (fun l : L => p ∈ l), m l = Δ - (t + 1)) :
    ∃ H : SimpleGraph (Fin (Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l)),
      H.Colorable 2 ∧ (∀ v, (H.neighborSet v).ncard = Δ) ∧ H.ediam ≤ 4 := by
  obtain ⟨H, hc, hd, he⟩ := regular_copy_graph G Δ hs ht hw hm
  have hcard : Fintype.card (Vtx P L w m) =
      Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l := by
    simp only [Vtx, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin]
    ring
  let e := Fintype.equivFinOfCardEq hcard
  obtain ⟨h1, h2, h3⟩ := regular_comap e H Δ hc hd he
  exact ⟨H.comap e.symm, h1, h2, h3⟩

end BipartiteDD.GQST
