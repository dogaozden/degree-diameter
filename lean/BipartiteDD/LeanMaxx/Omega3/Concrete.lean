import BipartiteDD.LeanMaxx.Omega3.Main
import BipartiteDD.LeanMaxx.Omega2.Polygon
import BipartiteDD.HexagonEven.Main

/-!
# Theorem 3.3 at the split Cayley hexagon `H(q)`

For every finite field `F` with `q = |F| ≥ 8` (any characteristic: `q = 8, 9, 11, 13, 16, …`), the incidence
graph of `H(q)` (points `SPt F`, lines `HLine F`) is a generalized hexagon of order `(q, q)` (`Hex`), so
`omega3_ediam` applies: whatever twisted labelling `lam : Copy α → Aut(H(q))` (colour-preserving
automorphisms = collineations) is used, `ΩH_q` has diameter at least `9`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open BipartiteDD.Hexagon BipartiteDD.HexagonEven BipartiteDD.LeanMaxx.Omega2

variable {F : Type*} [Field F] [Fintype F]

/-- The vertex type of the incidence graph of `H(q)` is nonempty. -/
theorem nonempty_hexagon : Nonempty (SPt F ⊕ HLine F) := by
  classical
  refine ⟨Sum.inl (sptOf (Pi.single 0 1 : V7 F) ?_ ?_)⟩
  · intro h
    have := congrFun h 0
    simp at this
  · simp [Qf]

/-- **The incidence graph of `H(q)` is a generalized hexagon of order `(q, q)`** (in the sense of `Hex`),
for every finite field. Classical instances are used for the finiteness and decidability data. -/
theorem hex_hexagon : ∃ (_ : Fintype (SPt F ⊕ HLine F)) (_ : DecidableEq (SPt F ⊕ HLine F))
    (_ : DecidableRel (BipartiteDD.Hexagon.incGraph (hexInc (F := F))).Adj),
    Hex (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass (Fintype.card F) := by
  classical
  haveI : Fintype (SPt F) := Fintype.ofFinite _
  haveI : Fintype (HLine F) := haveI := finite_hline_even (F := F); Fintype.ofFinite _
  have hB := genPolygonGraph_hexagon_even (F := F)
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  refine ⟨klass_proper, ?_, hB.egirth, reachable_of_ediam hB.ediam, dist_le_of_ediam hB.ediam⟩
  intro v
  rcases v with p | l
  · rw [degree_inl]; exact card_lines_through_even p
  · rw [degree_inr]; exact card_points_hline l

/-- **Theorem 3.3 for `H(q)`.** Let `F` be a finite field with `q = |F| ≥ 8`, `α ≥ 1` blocks with
`2 α ≤ q + 3`, any block types `typ`, `ε₀` the colour of the unbarred hubs (`0`: reading 2, `1`: its
point/line dual) and `lam c` an arbitrary collineation of `H(q)` for each copy `c`. Then `ΩH_q` has
diameter at least `9`. -/
theorem omega3_hexagon (hq : 8 ≤ Fintype.card F) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ Fintype.card F + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (lam : Copy α → autSub (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀
      (nfmk (fun c => (lam c : Equiv.Perm (SPt F ⊕ HLine F))))).ediam := by
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  haveI := nonempty_hexagon (F := F)
  exact omega3_ediam H hq hα h2 typ ε₀ lam

end BipartiteDD.LeanMaxx.Omega3
