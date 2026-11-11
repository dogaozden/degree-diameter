import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! # Layers around an edge (the Moore counting)

Fix a connected graph `G` on a finite vertex type, an edge `uv`, and a degree bound `d`. The layer
`L_i(u, v)` is the set of vertices `w` with `dist u w = i ≤ dist v w`.

* `|L_i| ≤ (d - 1) ^ i` (`card_layer_le`). `L_0 ⊆ {u}`. A vertex of `L_{i+1}` has a neighbour `p` with
  `dist u p = i`, and `p ∈ L_i` because `dist v p ≥ dist v w - 1 ≥ i`. A vertex `x ∈ L_i` has a neighbour
  `q ∉ L_{i+1}` (for `i = 0`, `q = v`, since `dist v v = 0`; for `i > 0`, the predecessor of `x` on a
  shortest path from `u`), so it has at most `d - 1` neighbours in `L_{i+1}`.
* If in addition every vertex is at distance `≤ D` from every other, and `dist u w ≠ dist v w` for all
  `w` (bipartiteness), then the layers `L_i(u, v)` and `L_i(v, u)` with `i < D` cover all vertices
  (`card_le_of_edge`). This gives `|V| ≤ 2 ∑_{j < D} (d - 1) ^ j`. -/

namespace BipartiteDD.LeanMaxx.Moore

open SimpleGraph Finset
open scoped Classical

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- The layer `L_i(u, v)`: the vertices at distance `i` from `u` and at distance at least `i` from `v`. -/
noncomputable def layer (G : SimpleGraph V) (u v : V) (i : ℕ) : Finset V :=
  univ.filter fun w => G.dist u w = i ∧ i ≤ G.dist v w

theorem mem_layer {u v w : V} {i : ℕ} :
    w ∈ layer G u v i ↔ G.dist u w = i ∧ i ≤ G.dist v w := by
  simp [layer]

omit [Fintype V] in
/-- A vertex at distance `k + 1` from `u` has a neighbour at distance `k` from `u`: the vertex before it
on a shortest walk from `u`. -/
theorem exists_parent (hc : G.Connected) {u x : V} {k : ℕ} (hx : G.dist u x = k + 1) :
    ∃ p, G.Adj x p ∧ G.dist u p = k := by
  obtain ⟨W, hW⟩ := hc.exists_walk_length_eq_dist x u
  rw [dist_comm, hx] at hW
  have key : ∀ (p : V) (h : G.Adj x p) (q : G.Walk p u), q.length = k → G.dist u p = k := by
    intro p h q hq
    apply le_antisymm
    · have := dist_le q.reverse
      rw [Walk.length_reverse, hq] at this
      exact this
    · have h1 := hc.dist_triangle (u := u) (v := p) (w := x)
      have h2 : G.dist p x = 1 := dist_eq_one_iff_adj.2 h.symm
      omega
  cases W with
  | nil => simp at hW
  | cons h q =>
    rw [Walk.length_cons] at hW
    exact ⟨_, h, key _ h q (by omega)⟩

/-- The only vertex at distance `0` from `u` is `u`. -/
theorem layer_zero_subset (hc : G.Connected) (u v : V) : layer G u v 0 ⊆ {u} := by
  intro w hw
  rw [mem_layer] at hw
  obtain ⟨W, hW⟩ := hc.exists_walk_length_eq_dist u w
  rw [hw.1] at hW
  exact mem_singleton.2 (Walk.eq_of_length_eq_zero hW).symm

/-- Every `x ∈ L_i` has a neighbour outside `L_{i+1}`. -/
theorem exists_forbidden (hc : G.Connected) {u v : V} (huv : G.Adj u v) {i : ℕ} {x : V}
    (hx : x ∈ layer G u v i) : ∃ q, G.Adj x q ∧ q ∉ layer G u v (i + 1) := by
  rw [mem_layer] at hx
  cases i with
  | zero =>
    have hxu : u = x := (hc.dist_eq_zero_iff).1 hx.1
    subst hxu
    refine ⟨v, huv, ?_⟩
    simp [mem_layer]
  | succ k =>
    obtain ⟨p, hxp, hp⟩ := exists_parent hc hx.1
    refine ⟨p, hxp, ?_⟩
    rw [mem_layer]
    intro h
    omega

/-- A vertex with at most `d` neighbours has at most `d - 1` neighbours in any finset that misses one of
its neighbours. -/
theorem card_filter_adj_le {d : ℕ} (hdeg : ∀ x, (univ.filter (G.Adj x)).card ≤ d) {x q : V}
    (hq : G.Adj x q) (T : Finset V) (hqT : q ∉ T) :
    (T.filter (G.Adj x)).card ≤ d - 1 := by
  have hsub : T.filter (G.Adj x) ⊆ (univ.filter (G.Adj x)).erase q := by
    intro w hw
    rw [mem_filter] at hw
    rw [mem_erase, mem_filter]
    refine ⟨fun h => hqT (h ▸ hw.1), mem_univ _, hw.2⟩
  calc (T.filter (G.Adj x)).card
      ≤ ((univ.filter (G.Adj x)).erase q).card := card_le_card hsub
    _ = (univ.filter (G.Adj x)).card - 1 := card_erase_of_mem (by simp [hq])
    _ ≤ d - 1 := Nat.sub_le_sub_right (hdeg x) 1

/-- **Layer bound.** In a connected graph of max degree `d`, the layer `L_i(u, v)` of an edge `uv` has at
most `(d - 1) ^ i` vertices. -/
theorem card_layer_le (hc : G.Connected) {u v : V} (huv : G.Adj u v) {d : ℕ}
    (hdeg : ∀ x, (univ.filter (G.Adj x)).card ≤ d) (i : ℕ) :
    (layer G u v i).card ≤ (d - 1) ^ i := by
  induction i with
  | zero =>
    exact (card_le_card (layer_zero_subset hc u v)).trans (by simp)
  | succ i ih =>
    have hsub : layer G u v (i + 1) ⊆
        (layer G u v i).biUnion fun x => (layer G u v (i + 1)).filter (G.Adj x) := by
      intro w hw
      rw [mem_biUnion]
      rw [mem_layer] at hw
      obtain ⟨hw1, hw2⟩ := hw
      obtain ⟨p, hpw, hp⟩ := exists_parent hc hw1
      refine ⟨p, ?_, ?_⟩
      · rw [mem_layer]
        refine ⟨hp, ?_⟩
        have h1 := hc.dist_triangle (u := v) (v := p) (w := w)
        have h2 : G.dist p w = 1 := dist_eq_one_iff_adj.2 hpw.symm
        omega
      · rw [mem_filter]
        exact ⟨mem_layer.2 ⟨hw1, hw2⟩, hpw.symm⟩
    calc (layer G u v (i + 1)).card
        ≤ ((layer G u v i).biUnion fun x => (layer G u v (i + 1)).filter (G.Adj x)).card :=
          card_le_card hsub
      _ ≤ ∑ x ∈ layer G u v i, ((layer G u v (i + 1)).filter (G.Adj x)).card :=
          card_biUnion_le
      _ ≤ ∑ _x ∈ layer G u v i, (d - 1) := by
          apply sum_le_sum
          intro x hx
          obtain ⟨q, hxq, hq⟩ := exists_forbidden hc huv hx
          exact card_filter_adj_le hdeg hxq _ hq
      _ = (layer G u v i).card * (d - 1) := by rw [sum_const, smul_eq_mul]
      _ ≤ (d - 1) ^ i * (d - 1) := Nat.mul_le_mul ih le_rfl
      _ = (d - 1) ^ (i + 1) := (pow_succ _ _).symm

/-- **Covering.** Let `uv` be an edge of a connected graph in which every vertex is within `D` of every
other, and in which no vertex is equidistant from `u` and `v` (bipartiteness). Then `|V| ≤ 2 ∑_{j<D} (d-1)^j`
for max degree `d`. -/
theorem card_le_of_edge (hc : G.Connected) {u v : V} (huv : G.Adj u v) {d D : ℕ}
    (hdeg : ∀ x, (univ.filter (G.Adj x)).card ≤ d) (hD : ∀ x y, G.dist x y ≤ D)
    (hpar : ∀ w, G.dist u w ≠ G.dist v w) :
    Fintype.card V ≤ 2 * ∑ j ∈ range D, (d - 1) ^ j := by
  have hcov : (univ : Finset V) ⊆
      (range D).biUnion (layer G u v) ∪ (range D).biUnion (layer G v u) := by
    intro w _
    rw [mem_union, mem_biUnion, mem_biUnion]
    have hne := hpar w
    rcases le_total (G.dist u w) (G.dist v w) with h | h
    · left
      refine ⟨G.dist u w, ?_, mem_layer.2 ⟨rfl, h⟩⟩
      rw [mem_range]
      have := hD v w
      omega
    · right
      refine ⟨G.dist v w, ?_, mem_layer.2 ⟨rfl, h⟩⟩
      rw [mem_range]
      have := hD u w
      omega
  have h1 := card_le_card hcov
  have h2 := card_union_le ((range D).biUnion (layer G u v)) ((range D).biUnion (layer G v u))
  have h3 : ((range D).biUnion (layer G u v)).card ≤ ∑ j ∈ range D, (d - 1) ^ j :=
    card_biUnion_le.trans (sum_le_sum fun i _ => card_layer_le hc huv hdeg i)
  have h4 : ((range D).biUnion (layer G v u)).card ≤ ∑ j ∈ range D, (d - 1) ^ j :=
    card_biUnion_le.trans (sum_le_sum fun i _ => card_layer_le hc huv.symm hdeg i)
  rw [card_univ] at h1
  omega

end BipartiteDD.LeanMaxx.Moore
