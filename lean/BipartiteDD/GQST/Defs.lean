import BipartiteDD.GQ4.Defs

/-! Group GQST, part 1: generalized quadrangles of order `(s, t)` and their incidence graphs.

A point lies on `t + 1` lines and a line carries `s + 1` points. The axioms are those of `GQ` with two
parameters; as there, the uniqueness half of the GQ axiom is not recorded. -/

namespace BipartiteDD

/-- A finite generalized quadrangle of order `(s, t)`, given by its incidence relation. -/
structure GQst (P L : Type*) [Membership P L] (s t : ℕ) : Prop where
  pts_on_line : ∀ l : L, Nat.card {p : P // p ∈ l} = s + 1
  lines_on_pt : ∀ p : P, Nat.card {l : L // p ∈ l} = t + 1
  one_line : ∀ (p r : P) (l m : L), p ∈ l → r ∈ l → p ∈ m → r ∈ m → p = r ∨ l = m
  gq_ax : ∀ (p : P) (l : L), p ∉ l → ∃ x : P, x ∈ l ∧ ∃ m : L, p ∈ m ∧ x ∈ m

namespace GQst

variable {P L : Type*} [Membership P L] {s t : ℕ}

/-- Every point lies on a line. -/
theorem exists_line (G : GQst P L s t) (p : P) : ∃ l : L, p ∈ l := by
  have hpos : 0 < Nat.card {l : L // p ∈ l} := by rw [G.lines_on_pt p]; omega
  obtain ⟨⟨l, hl⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨l, hl⟩

/-- Every line carries a point. -/
theorem exists_pt (G : GQst P L s t) (l : L) : ∃ p : P, p ∈ l := by
  have hpos : 0 < Nat.card {p : P // p ∈ l} := by rw [G.pts_on_line l]; omega
  obtain ⟨⟨p, hp⟩⟩ := (Nat.card_pos_iff.mp hpos).1
  exact ⟨p, hp⟩

/-- Every vertex of the incidence graph has a neighbour. -/
theorem exists_nbr (G : GQst P L s t) (w : P ⊕ L) : ∃ u, (incGraph P L).Adj w u := by
  rcases w with p | l
  · obtain ⟨l, hl⟩ := G.exists_line p
    exact ⟨.inr l, incGraph_adj_inl_inr.2 hl⟩
  · obtain ⟨p, hp⟩ := G.exists_pt l
    exact ⟨.inl p, incGraph_adj_inr_inl.2 hp⟩

end GQst

end BipartiteDD
