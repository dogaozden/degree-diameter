import BipartiteDD.LeanMaxx.Omega2.Axioms
open BipartiteDD BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2
open scoped Classical

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
instance : NeZero (2 : ZMod 7) := ⟨by decide⟩
instance : NeZero (2 : ZMod 11) := ⟨by decide⟩

-- Concrete: toy graph over the incidence graph of H(7) and H(11) with any bijection σ (explicit, non-abstract).
theorem concrete (p : ℕ) [Fact p.Prime] [NeZero (2 : ZMod p)] (hp : 7 ≤ p) (σ : SPt (ZMod p) ≃ HLine (ZMod p)) (t : SPt (ZMod p) ⊕ HLine (ZMod p)) :
    ∃ (W : Type) (G : SimpleGraph W), 9 ≤ G.ediam := by
  haveI : Fintype (SPt (ZMod p)) := Fintype.ofFinite _
  haveI : Fintype (HLine (ZMod p)) := haveI := finite_hline (F := ZMod p); Fintype.ofFinite _
  have hdeg : ∀ v, (incGraph (hexInc (F := ZMod p))).degree v = p + 1 := by
    intro v; rcases v with a | l
    · rw [degree_inl]; exact (card_lines_through a).trans (by rw [ZMod.card])
    · rw [degree_inr]; exact (card_points_hline l).trans (by rw [ZMod.card])
  have H := HexData.of_polygon (genPolygonGraph_hexagon (F := ZMod p)) hdeg klass_proper
  exact ⟨_, _, omega2_toy H hp (partner_partner σ) (klass_partner σ) t⟩

#print axioms concrete
