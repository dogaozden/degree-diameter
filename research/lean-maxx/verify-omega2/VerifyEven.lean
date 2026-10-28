import BipartiteDD.LeanMaxx.Omega2.Axioms
import BipartiteDD.HexagonEven.Main
open BipartiteDD BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2

/-- Even characteristic too: Theorem 2 for H(q), every finite field F with |F| ≥ 7. -/
theorem omega2_even {F : Type*} [Field F] [Fintype F] {V ι : Type*} (hq : 7 ≤ Fintype.card F)
    (σ : SPt F ≃ HLine F)
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
  haveI : Fintype (HLine F) := haveI := HexagonEven.finite_hline_even (F := F); Fintype.ofFinite _
  exact omega2_ediam_inc (inc := hexInc (F := F)) HexagonEven.genPolygonGraph_hexagon_even (q := Fintype.card F) hq
    (fun p => HexagonEven.card_lines_through_even p) (fun W => card_points_hline W) σ hK h1 h2 hsurj hconn hx hmiss
#print axioms omega2_even
