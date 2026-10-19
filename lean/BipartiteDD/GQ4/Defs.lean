import Mathlib.Combinatorics.SimpleGraph.Diam
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! Group GQ4, part 1: generalized quadrangles and their incidence graphs.
See `research/gq4/THEOREM.md`, Setting. Only the axioms used for the diameter and degree bounds
are needed; the uniqueness half of the GQ axiom is recorded in `GQ` but never used. -/

namespace BipartiteDD

/-- A finite generalized quadrangle of order `(q, q)`, given by its incidence relation. -/
structure GQ (P L : Type*) [Membership P L] (q : ℕ) : Prop where
  pts_on_line : ∀ l : L, Nat.card {p : P // p ∈ l} = q + 1
  lines_on_pt : ∀ p : P, Nat.card {l : L // p ∈ l} = q + 1
  one_line : ∀ (p r : P) (l m : L), p ∈ l → r ∈ l → p ∈ m → r ∈ m → p = r ∨ l = m
  gq_ax : ∀ (p : P) (l : L), p ∉ l → ∃ x : P, x ∈ l ∧ ∃ m : L, p ∈ m ∧ x ∈ m

variable {P L : Type*} [Membership P L]

/-- The incidence graph on `P ⊕ L`: a point `inl p` and a line `inr l` are adjacent iff `p ∈ l`. -/
def incGraph (P L : Type*) [Membership P L] : SimpleGraph (P ⊕ L) :=
  SimpleGraph.fromRel fun x y => ∃ p l, x = .inl p ∧ y = .inr l ∧ p ∈ l

theorem incGraph_adj_inl_inr {p : P} {l : L} : (incGraph P L).Adj (.inl p) (.inr l) ↔ p ∈ l := by
  simp [incGraph, SimpleGraph.fromRel_adj]

theorem incGraph_adj_inr_inl {p : P} {l : L} : (incGraph P L).Adj (.inr l) (.inl p) ↔ p ∈ l := by
  rw [SimpleGraph.adj_comm]
  exact incGraph_adj_inl_inr

theorem incGraph_not_adj_inl_inl {p q : P} : ¬ (incGraph P L).Adj (.inl p) (.inl q) := by
  simp [incGraph, SimpleGraph.fromRel_adj]

theorem incGraph_not_adj_inr_inr {l m : L} : ¬ (incGraph P L).Adj (.inr l) (.inr m) := by
  simp [incGraph, SimpleGraph.fromRel_adj]

/-- Adjacent vertices of the incidence graph lie on opposite sides. -/
theorem incGraph_isLeft_ne {a b : P ⊕ L} (h : (incGraph P L).Adj a b) : a.isLeft ≠ b.isLeft := by
  rcases a with p | l <;> rcases b with q | m
  · exact (incGraph_not_adj_inl_inl h).elim
  · simp
  · simp
  · exact (incGraph_not_adj_inr_inr h).elim

namespace GQ

variable {q : ℕ}

/-- Every point lies on a line. -/
theorem exists_line (G : GQ P L q) (p : P) : ∃ l : L, p ∈ l := by
  have hpos : 0 < Nat.card {l : L // p ∈ l} := by rw [G.lines_on_pt p]; omega
  obtain ⟨⟨l, hl⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨l, hl⟩

/-- Every line carries a point. -/
theorem exists_pt (G : GQ P L q) (l : L) : ∃ p : P, p ∈ l := by
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by rw [G.pts_on_line l]; omega
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨p, hp⟩

/-- Every vertex of the incidence graph has a neighbour. -/
theorem exists_nbr (G : GQ P L q) (w : P ⊕ L) : ∃ u, (incGraph P L).Adj w u := by
  rcases w with p | l
  · obtain ⟨l, hl⟩ := G.exists_line p
    exact ⟨.inr l, incGraph_adj_inl_inr.2 hl⟩
  · obtain ⟨p, hp⟩ := G.exists_pt l
    exact ⟨.inl p, incGraph_adj_inr_inl.2 hp⟩

end GQ

end BipartiteDD
