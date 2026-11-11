import BipartiteDD.LeanMaxx.Omega45.Geometric7
import BipartiteDD.LeanMaxx.Omega3.Concrete

/-!
# `q = 7` at the split Cayley hexagon `H(7)`

The unconditional `q = 7` result of `Q7.lean` for the actual hexagon `H(F)`, `|F| = 7` (`F = ZMod 7`, or any
field with seven elements): with at most four blocks of five copies, every geometric labelling of the wiring
gives diameter `≥ 9`. (The case `α = 5`, Gómez's wiring, is Theorem 4.5 of the note; it is proved in
`Q7.lean` only modulo Lemmas 4.3 and 4.4, see `research/lean-maxx/STATUS-omega45.md`.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open BipartiteDD.Hexagon BipartiteDD.HexagonEven BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {F : Type*} [Field F] [Fintype F]

/-- `q = 7`, `α ≤ 4`, twisted labellings, at `H(7)`. -/
theorem omega45_hexagon_alpha_le_four (hq : Fintype.card F = 7) {α : ℕ} (hα : 0 < α) (hα4 : α ≤ 4)
    (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (lam : Copy α → autSub (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀
      (nfmk (fun c => (lam c : Equiv.Perm (SPt F ⊕ HLine F))))).ediam := by
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  haveI := nonempty_hexagon (F := F)
  rw [hq] at H
  obtain ⟨x, y, h⟩ := omega45_alpha_le_four H hα hα4 typ ε₀ lam
  exact h.trans SimpleGraph.edist_le_ediam

/-- `q = 7`, `α ≤ 4`, geometric labellings (all transfer maps induced by automorphisms of the incidence graph
of `H(7)`), at `H(7)`. -/
theorem omega45_hexagon_geometric_alpha_le_four (hq : Fintype.card F = 7) {α : ℕ} (hα : 0 < α)
    (hα4 : α ≤ 4) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (μ : Copy α → Equiv.Perm (SPt F ⊕ HLine F)) (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : Geometric (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass μ) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀ (labMk μ)).ediam := by
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  haveI := nonempty_hexagon (F := F)
  rw [hq] at H
  exact omega45_geometric_alpha_le_four H hα hα4 typ ε₀ μ hμ hgeo

/-- `q = 7`, `α ≤ 4`, with the note's definition of a geometric labelling (transfers along shared hub
classes), at `H(7)`. -/
theorem omega45_hexagon_geometric_shared_alpha_le_four (hq : Fintype.card F = 7) {α : ℕ} (hα : 0 < α)
    (hα4 : α ≤ 4) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (μ : Copy α → Equiv.Perm (SPt F ⊕ HLine F)) (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : GeometricShared typ (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass ε₀ μ) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀ (labMk μ)).ediam :=
  omega45_hexagon_geometric_alpha_le_four hq hα hα4 typ ε₀ μ hμ (geometric_of_shared μ hgeo)

end BipartiteDD.LeanMaxx.Omega45
