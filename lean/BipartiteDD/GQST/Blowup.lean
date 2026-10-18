import BipartiteDD.GQST.Diam
import BipartiteDD.GQ4.Blowup

/-! Group GQST, part 3: the weighted copy graph of a generalized quadrangle of order `(s, t)`.

Vertices: points `P` and `w p` copies of each point `p` on the point side; lines `L` and `m l` copies of
each line `l` on the line side. A copy is adjacent to the original vertices it meets in `incGraph`, and
nothing else (this is `GQ4.copyGraph`, with the copy-graph lemmas of `GQ4.Copy` reused). Copies of
the same point may be several; a point may be copied twice when `w p = 2`.

Bipartite: the point side and the line side are the two colour classes. Diameter: from `copyGraph`. -/

namespace BipartiteDD.GQST

open SimpleGraph
open scoped Classical

variable {P L : Type*} [Membership P L]

/-- The underlying original vertex (a point or line of the quadrangle) of a vertex of the copy graph. -/
def under {w : P → ℕ} {m : L → ℕ} :
    (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)) → P ⊕ L
  | .inl (.inl p) => .inl p
  | .inl (.inr x) => .inl x.1
  | .inr (.inl l) => .inr l
  | .inr (.inr x) => .inr x.1

/-- The original (not copied) vertices. -/
def isOrig {w : P → ℕ} {m : L → ℕ} :
    (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l)) → Prop
  | .inl (.inl _) => True
  | .inl (.inr _) => False
  | .inr (.inl _) => True
  | .inr (.inr _) => False

/-- The original vertex over a point or line. -/
def origOf (w : P → ℕ) (m : L → ℕ) :
    P ⊕ L → (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))
  | .inl p => .inl (.inl p)
  | .inr l => .inr (.inl l)

omit [Membership P L] in
theorem under_origOf (w : P → ℕ) (m : L → ℕ) (x : P ⊕ L) :
    under (origOf w m x) = x := by
  cases x <;> rfl

omit [Membership P L] in
theorem isOrig_origOf (w : P → ℕ) (m : L → ℕ) (x : P ⊕ L) :
    isOrig (origOf w m x) := by
  cases x <;> trivial

/-- The weighted copy graph: `x ~ y` iff their underlying vertices are adjacent in the incidence graph
and one of them is original. -/
def blowup (P L : Type*) [Membership P L] (w : P → ℕ) (m : L → ℕ) :
    SimpleGraph ((P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))) :=
  GQ4.copyGraph (incGraph P L) (under (w := w) (m := m)) (isOrig (w := w) (m := m))

/-- Adjacency in the copy graph, unfolded. -/
theorem blowup_adj_iff {w : P → ℕ} {m : L → ℕ}
    {u v : (P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))} :
    (blowup P L w m).Adj u v ↔
      (incGraph P L).Adj (under u) (under v) ∧ (isOrig u ∨ isOrig v) :=
  Iff.rfl

/-- The copy graph is bipartite: points and copies of points on one side, lines and copies of lines on
the other. -/
theorem blowup_colorable (w : P → ℕ) (m : L → ℕ) : (blowup P L w m).Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => if (under (w := w) (m := m) v).isLeft then (0 : Fin 2) else 1) ?_⟩
  intro u v h
  have h1 : (incGraph P L).Adj (under u) (under v) := (blowup_adj_iff.1 h).1
  have hne := incGraph_isLeft_ne h1
  cases hu : (under (w := w) (m := m) u).isLeft <;>
    cases hv : (under (w := w) (m := m) v).isLeft <;> simp_all

/-- The copy graph has diameter at most `4`. -/
theorem blowup_ediam {s t : ℕ} (G : GQst P L s t) (w : P → ℕ) (m : L → ℕ) :
    (blowup P L w m).ediam ≤ 4 :=
  GQ4.ediam_le_four_of_copy (s := origOf w m) (under_origOf w m) (isOrig_origOf w m)
    G.exists_nbr (G.ediam_le_four)

end BipartiteDD.GQST
