import BipartiteDD.Basic
import BipartiteDD.LeanMaxx.Moore.Layers
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-! # The bipartite Moore bound

For a bipartite graph of maximum degree `d ≥ 2` and diameter at most `D ≥ 1`, the number of vertices is at
most `2 ∑_{j<D} (d-1)^j`. Proof: if there is no edge, the graph has at most one vertex. Otherwise fix an
edge `uv` and apply `card_le_of_edge` (`Layers.lean`). Bipartiteness gives the colouring that rules out
`dist u w = dist v w`. -/

namespace BipartiteDD.LeanMaxx.Moore

open SimpleGraph Finset
open scoped Classical

/-- **Bipartite Moore bound.** A bipartite graph on a finite type `V` with every degree at most `d`, and
diameter at most `D`, has at most `2 ∑_{j<D} (d-1)^j` vertices. -/
theorem card_le_moore {V : Type*} [Fintype V] (G : SimpleGraph V) {d D : ℕ} (hd : 2 ≤ d)
    (hD : 1 ≤ D) (h : BipartiteDD.IsBipartiteDegDiam G d D) :
    Fintype.card V ≤ 2 * ∑ j ∈ range D, (d - 1) ^ j := by
  obtain ⟨hcol, hdeg', hdiam⟩ := h
  have hdeg : ∀ x, (univ.filter (G.Adj x)).card ≤ d := fun x => by
    have hset : G.neighborSet x = ↑(univ.filter (G.Adj x)) := by ext y; simp
    have h := hdeg' x
    rw [hset, Set.ncard_coe_finset] at h
    exact h
  have hreach : ∀ x y, G.Reachable x y := fun x y =>
    edist_ne_top_iff_reachable.1
      (ne_top_of_le_ne_top (ENat.natCast_ne_top D) ((edist_le_ediam (u := x) (v := y)).trans hdiam))
  have hD : ∀ x y, G.dist x y ≤ D := fun x y => by
    have h1 : G.edist x y ≤ D := (edist_le_ediam (u := x) (v := y)).trans hdiam
    exact_mod_cast (natCast_dist_le_edist (u := x) (v := y)).trans h1
  by_cases hE : ∃ x y, G.Adj x y
  · obtain ⟨u, v, huv⟩ := hE
    have : Nonempty V := ⟨u⟩
    have hc : G.Connected := ⟨hreach⟩
    -- the 2-colouring, as a `Bool`-colouring
    obtain ⟨C⟩ := hcol
    let c : G.Coloring Bool := SimpleGraph.Coloring.mk (fun x => decide (C x = 0)) fun {a b} hab hEq => by
      have key : ∀ x y : Fin 2, (x = 0 ↔ y = 0) → x = y := by decide
      exact SimpleGraph.Coloring.valid C hab (key _ _ (decide_eq_decide.1 hEq))
    -- bipartiteness: `dist u w` and `dist v w` have different parity
    have hpar : ∀ w, G.dist u w ≠ G.dist v w := by
      intro w heq
      obtain ⟨P, hP⟩ := hc.exists_walk_length_eq_dist u w
      obtain ⟨Q, hQ⟩ := hc.exists_walk_length_eq_dist v w
      have hPe := SimpleGraph.Coloring.even_length_iff_congr c P
      have hQe := SimpleGraph.Coloring.even_length_iff_congr c Q
      rw [hP, heq] at hPe
      rw [hQ] at hQe
      have hcuv : c u ≠ c v := SimpleGraph.Coloring.valid c huv
      have key2 : ∀ a b x : Bool, a ≠ b → ¬((a ↔ x) ↔ (b ↔ x)) := by decide
      exact key2 _ _ _ hcuv (hPe.symm.trans hQe)
    exact card_le_of_edge hc huv hdeg hD hpar
  · -- no edge: a connected graph with no edge has at most one vertex
    have hsub : Subsingleton V := by
      refine ⟨fun x y => ?_⟩
      by_contra hxy
      obtain ⟨W⟩ := hreach x y
      cases W with
      | nil => exact hxy rfl
      | cons h _ => exact hE ⟨_, _, h⟩
    have h1 : Fintype.card V ≤ 1 := Fintype.card_le_one_iff_subsingleton.2 hsub
    have h2 : 1 ≤ ∑ j ∈ range D, (d - 1) ^ j := by
      have := single_le_sum (f := fun j => (d - 1) ^ j) (fun j _ => Nat.zero_le _)
        (mem_range.2 (by omega : 0 < D))
      simpa using this
    omega

/-- **Corollary for regular graphs.** A bipartite graph in which every vertex has exactly `d` neighbours
and whose diameter is at most `D` has at most `2 ∑_{j<D} (d-1)^j` vertices. This is `card_le_moore`
applied to the degree bound `≤ d`, which holds with equality. -/
theorem card_le_moore_of_regular {V : Type*} [Fintype V] (G : SimpleGraph V) {d D : ℕ} (hd : 2 ≤ d)
    (hD : 1 ≤ D) (hreg : ∀ v, (G.neighborSet v).ncard = d) (hcol : G.Colorable 2)
    (hdiam : G.ediam ≤ D) :
    Fintype.card V ≤ 2 * ∑ j ∈ range D, (d - 1) ^ j :=
  card_le_moore G hd hD ⟨hcol, fun v => (hreg v).le, hdiam⟩

end BipartiteDD.LeanMaxx.Moore
