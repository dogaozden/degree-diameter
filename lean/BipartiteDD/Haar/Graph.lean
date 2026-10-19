import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Haar graphs. For a group `G` and a finite set `S ⊆ G`, the Haar graph has vertex set `G ⊕ G`:
`inl g` is `(g, A)` and `inr h` is `(h, B)`. The vertex `(g, A)` is adjacent to `(s * g, B)` for
`s ∈ S`, and there are no other edges. Equivalently `(g, A) ~ (h, B)` iff `h * g⁻¹ ∈ S`.

Left multiplication is not an automorphism of this graph, but right multiplication is: it preserves
`h * g⁻¹`. -/

namespace BipartiteDD.Haar

variable {G : Type*} [Group G]

/-- The edge relation, read from the `A` side: `inl g` is related to `inr h` iff `h * g⁻¹ ∈ S`. -/
def haarRel (S : Finset G) : G ⊕ G → G ⊕ G → Prop
  | .inl g, .inr h => h * g⁻¹ ∈ S
  | _, _ => False

/-- The Haar graph of `S`, on `G ⊕ G`. `fromRel` symmetrises the relation and drops loops. -/
def haarGraph (S : Finset G) : SimpleGraph (G ⊕ G) :=
  SimpleGraph.fromRel (haarRel S)

theorem haarGraph_adj_inl_inr (S : Finset G) (g h : G) :
    (haarGraph S).Adj (.inl g) (.inr h) ↔ h * g⁻¹ ∈ S := by
  simp [haarGraph, haarRel, SimpleGraph.fromRel_adj]

theorem haarGraph_adj_inr_inl (S : Finset G) (g h : G) :
    (haarGraph S).Adj (.inr h) (.inl g) ↔ h * g⁻¹ ∈ S := by
  rw [SimpleGraph.adj_comm, haarGraph_adj_inl_inr]

theorem haarGraph_not_adj_inl_inl (S : Finset G) (g g' : G) :
    ¬ (haarGraph S).Adj (.inl g) (.inl g') := by
  simp [haarGraph, haarRel, SimpleGraph.fromRel_adj]

theorem haarGraph_not_adj_inr_inr (S : Finset G) (h h' : G) :
    ¬ (haarGraph S).Adj (.inr h) (.inr h') := by
  simp [haarGraph, haarRel, SimpleGraph.fromRel_adj]

end BipartiteDD.Haar
