import BipartiteDD.GQ4.Copy
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Data.Set.Card

/-! Group GQ4, part 4: the concrete copy graph of a generalized quadrangle.

Vertices: points `P` and `j` copies of each point of `O` on the point side; lines `L` and `m l` copies
of each line `l` on the line side. A copy is adjacent to the original vertices it meets in `incGraph`,
and nothing else; so copies are never adjacent to copies.

Bipartite: the point side and the line side are the two colour classes. Degrees: a copy has degree
`q + 1`; an original point has `q + 1` original lines and `∑ m` line copies through it; an original line
has `q + 1` original points and `j` copies per point of `O` on it. Diameter: from `copyGraph`. -/

namespace BipartiteDD.GQ4

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- The underlying original vertex (a point or line of the quadrangle) of a vertex of the copy graph. -/
def under {O : Finset P} {j : ℕ} {m : L → ℕ} :
    (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l)) → P ⊕ L
  | .inl (.inl p) => .inl p
  | .inl (.inr (x, _)) => .inl x.1
  | .inr (.inl l) => .inr l
  | .inr (.inr ⟨l, _⟩) => .inr l

/-- The original (not copied) vertices. -/
def isOrig {O : Finset P} {j : ℕ} {m : L → ℕ} :
    (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l)) → Prop
  | .inl (.inl _) => True
  | .inl (.inr _) => False
  | .inr (.inl _) => True
  | .inr (.inr _) => False

/-- The original vertex over a point or line. -/
def origOf (O : Finset P) (j : ℕ) (m : L → ℕ) :
    P ⊕ L → (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))
  | .inl p => .inl (.inl p)
  | .inr l => .inr (.inl l)

theorem under_origOf (O : Finset P) (j : ℕ) (m : L → ℕ) (w : P ⊕ L) :
    under (origOf O j m w) = w := by
  cases w <;> rfl

theorem isOrig_origOf (O : Finset P) (j : ℕ) (m : L → ℕ) (w : P ⊕ L) :
    isOrig (origOf O j m w) := by
  cases w <;> trivial

/-- The copy graph: `x ~ y` iff their underlying vertices are adjacent in the incidence graph and one
of them is original. -/
def blowup (P L : Type*) [Membership P L] (O : Finset P) (j : ℕ) (m : L → ℕ) :
    SimpleGraph ((P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))) :=
  copyGraph (incGraph P L) under isOrig

/-- Adjacency in the blow-up, unfolded. -/
theorem blowup_adj_iff {O : Finset P} {j : ℕ} {m : L → ℕ} {u v : (P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))} :
    (blowup P L O j m).Adj u v ↔ (incGraph P L).Adj (under u) (under v) ∧ (isOrig u ∨ isOrig v) :=
  Iff.rfl

/-- The blow-up is bipartite: points and copies of points on one side, lines and copies of lines on
the other. -/
theorem blowup_colorable (O : Finset P) (j : ℕ) (m : L → ℕ) :
    (blowup P L O j m).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if (under v).isLeft then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  have h1 : (incGraph P L).Adj (under u) (under v) := (blowup_adj_iff.1 h).1
  have hne := incGraph_isLeft_ne h1
  cases hu : (under u).isLeft <;> cases hv : (under v).isLeft <;> simp_all

/-- The blow-up has diameter at most `4`. -/
theorem blowup_ediam [Fintype P] [Fintype L] {q : ℕ} (G : GQ P L q) (O : Finset P) (j : ℕ)
    (m : L → ℕ) : (blowup P L O j m).ediam ≤ 4 :=
  ediam_le_four_of_copy (s := origOf O j m) (under_origOf O j m) (isOrig_origOf O j m)
    G.exists_nbr (G.ediam_le_four)

/-- A finite set has at most `Fintype.card` many images of a function. -/
theorem ncard_le_of_subset_range {V D : Type*} [Fintype D] (N : Set V) (g : D → V)
    (h : N ⊆ Set.range g) : N.ncard ≤ Fintype.card D := by
  have h1 : (Set.range g).ncard ≤ Nat.card D := by
    rw [← Set.image_univ, ← Set.ncard_univ D]
    exact Set.ncard_image_le
  calc N.ncard ≤ (Set.range g).ncard := Set.ncard_le_ncard h (Set.finite_range g)
    _ ≤ Nat.card D := h1
    _ = Fintype.card D := Nat.card_eq_fintype_card

end BipartiteDD.GQ4
