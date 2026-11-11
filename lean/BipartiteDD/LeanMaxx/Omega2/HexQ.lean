import BipartiteDD.LeanMaxx.Omega2.Polygon

/-!
# Theorem 2 at the split Cayley hexagon `H(q)`

For a finite field `F` of odd characteristic with `q = |F| ≥ 7`, the points and lines of `H(q)` are in
bijection (`exists_sigma`), and Theorem 2 (`omega2_ediam_inc`) applies to the incidence graph of `H(q)`
with every such bijection `σ`.
-/

namespace BipartiteDD.LeanMaxx.Omega2

open BipartiteDD.Hexagon

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)]

theorem exists_sigma : Nonempty (SPt F ≃ HLine F) := by
  classical
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline (F := F); Fintype.ofFinite _
  refine ⟨Fintype.equivOfCardEq ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_spt_div, card_hline]

/-- **Theorem 2 at `H(q)`**, `q = |F| ≥ 7` odd: whatever bijection `σ` pairs points with lines, any graph
`G` built from copies of the incidence graph of `H(q)` and new vertices joined only to point `t` and
line `σ t` has a pair of vertices at distance `≥ 9`. -/
theorem omega2_ediam_hexagon {V ι : Type*} (hq : 7 ≤ Fintype.card F) (σ : SPt F ≃ HLine F)
    {G : SimpleGraph V} {f : V → SPt F ⊕ HLine F} {c : V → Option ι} {K : V → ZMod 2}
    (hK : ∀ u v, G.Adj u v → K u ≠ K v)
    (h1 : ∀ u w i j, G.Adj u w → c u = some i → c w = some j →
      i = j ∧ (Hexagon.incGraph (hexInc (F := F))).Adj (f u) (f w))
    (h2 : ∀ x w, G.Adj x w → c x = none →
      c w ≠ none ∧ (f w = f x ∨ f w = partner σ (f x)))
    (hsurj : ∀ j s, ∃ v, c v = some j ∧ f v = s)
    (hconn : ∀ j u v, c u = some j → c v = some j →
      ∃ p : G.Walk u v, ∀ z ∈ p.support, c z ≠ none)
    {x : V} (hx : c x = none) {j : ι} (hmiss : ∀ w, G.Adj x w → c w ≠ some j) :
    (9 : ℕ∞) ≤ G.ediam := by
  classical
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline (F := F); Fintype.ofFinite _
  exact omega2_ediam_inc (inc := hexInc (F := F)) genPolygonGraph_hexagon (q := Fintype.card F) hq
    (fun p => card_lines_through p) (fun W => card_points_hline W) σ hK h1 h2 hsurj hconn hx hmiss

end BipartiteDD.LeanMaxx.Omega2
