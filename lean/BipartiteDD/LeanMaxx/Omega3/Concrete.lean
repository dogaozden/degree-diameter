import BipartiteDD.LeanMaxx.Omega3.Main
import BipartiteDD.LeanMaxx.Omega3.Geometric
import BipartiteDD.LeanMaxx.Omega3.Shared
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


/-- **Theorem 3.3 for `H(q)`, geometric labellings.** For a finite field `F` with `q = |F| ≥ 8`, `α ≥ 1`
blocks with `2 α ≤ q + 3`, any block types, and any colour-preserving labelling `μ` of the copies (one
bijection `μ c` of the points and lines of `H(q)` per copy `c`) all of whose transfer maps are induced by
automorphisms of the incidence graph of `H(q)` (collineations, or dualities), `ΩH_q` has diameter at
least `9`. This is the statement of Theorem 3.3 of `research/theorems/OMEGA_REPAIR.md`, in reading 2
(`ε₀ = 0`) and in its point/line dual (`ε₀ = 1`). -/
theorem omega3_hexagon_geometric (hq : 8 ≤ Fintype.card F) {α : ℕ} (hα : 0 < α)
    (h2 : 2 * α ≤ Fintype.card F + 3) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (μ : Copy α → Equiv.Perm (SPt F ⊕ HLine F)) (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : Geometric (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass μ) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀ (labMk μ)).ediam := by
  obtain ⟨_, _, _, H⟩ := hex_hexagon (F := F)
  haveI := nonempty_hexagon (F := F)
  exact omega3_geometric H hq hα h2 typ ε₀ μ hμ hgeo


/-- **Theorem 3.3 of `research/theorems/OMEGA_REPAIR.md`, formalised.** Let `F` be a finite field with
`q = |F| ≥ 8` (so `q = 8, 9, 11, 13, 16, …`), `α ≥ 1` blocks of five copies with `2 α ≤ q + 3` (Gómez's
wiring has `α = ⌊(q + 3) / 2⌋`), any block types `typ` (type a or b), and `ε₀` the colour of the unbarred
hubs (`ε₀ = 0`: reading 2, unbarred hubs on points and barred hubs on lines; `ε₀ = 1`: its dual). Give
each copy `c` a colour-preserving bijection `μ c` of the points and lines of `H(q)` (the labelling) such
that every transfer map of every hub class (the map from the mark of a row in one copy met by the class to
its mark in another) is the restriction of an automorphism of the incidence graph of `H(q)`. Then the
graph `ΩH_q` has diameter at least `9`. -/
theorem omega3_hexagon_geometric_shared (hq : 8 ≤ Fintype.card F) {α : ℕ} (hα : 0 < α)
    (h2 : 2 * α ≤ Fintype.card F + 3) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (μ : Copy α → Equiv.Perm (SPt F ⊕ HLine F)) (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : GeometricShared typ (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass ε₀ μ) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀ (labMk μ)).ediam :=
  omega3_hexagon_geometric hq hα h2 typ ε₀ μ hμ (geometric_of_shared μ hgeo)

/-- Sanity check: the thesis labelling (all copies labelled alike, `μ c = 1`) is geometric, so Gómez's
`ΩH_q` as defined has diameter at least `9` for `q ≥ 8` (cf. Theorem 1 of `d12D8_table.md`). -/
theorem omega3_hexagon_thesis (hq : 8 ≤ Fintype.card F) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ Fintype.card F + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) :
    (9 : ℕ∞) ≤ (omega (BipartiteDD.Hexagon.incGraph (hexInc (F := F))) klass typ ε₀
      (labMk (fun _ => (1 : Equiv.Perm (SPt F ⊕ HLine F))))).ediam :=
  omega3_hexagon_geometric_shared hq hα h2 typ ε₀ _ (fun _ _ => rfl)
    (fun _ _ _ _ _ _ => ⟨1, fun _ _ => Iff.rfl, fun _ _ => rfl⟩)

end BipartiteDD.LeanMaxx.Omega3
