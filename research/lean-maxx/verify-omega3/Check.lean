import BipartiteDD.LeanMaxx.Omega3.Concrete

/-!
Verifier's scratch file for `leanmaxx-verify-omega3` (not part of the library; run with
`cd lean && lake env lean ../research/lean-maxx/verify-omega3/Check.lean`).

1. Prints the statements of the headline theorems.
2. Instantiates the headline theorem at Gómez's `α = ⌊(q+3)/2⌋` for an arbitrary finite field with `q ≥ 8`.
3. Satisfiability witness: any family of colour-preserving collineations `g c` is a `GeometricShared` labelling.
4. Fully concrete instances `q = 11` (`ZMod 11`) and `q = 8` (`GaloisField 2 3`), thesis labelling.
-/

open BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega2 BipartiteDD.Hexagon BipartiteDD.HexagonEven

set_option pp.proofs.withType false

#check @omega3_hexagon_geometric_shared
#print GeometricShared
#print omega
#print omegaRel
#print metPos
#print Hex

/-- 2. Gómez's `α = ⌊(q+3)/2⌋`, any block types, any `ε₀`, any geometric (shared-transfer) labelling. -/
theorem gomez_alpha {F : Type*} [Field F] [Fintype F] (hq : 8 ≤ Fintype.card F)
    (typ : Fin ((Fintype.card F + 3) / 2) → Bool) (ε₀ : ZMod 2)
    (μ : Copy ((Fintype.card F + 3) / 2) → Equiv.Perm (SPt F ⊕ HLine F))
    (hμ : ∀ c u, klass (μ c u) = klass u)
    (hgeo : GeometricShared typ (incGraph (hexInc (F := F))) klass ε₀ μ) :
    (9 : ℕ∞) ≤ (omega (incGraph (hexInc (F := F))) klass typ ε₀ (labMk μ)).ediam :=
  omega3_hexagon_geometric_shared hq (by omega) (by omega) typ ε₀ μ hμ hgeo

/-- 3. Satisfiability: every family of colour-preserving collineations is a geometric labelling in the
note's sense (transfer of any class from `c` to `d` is `g d * (g c)⁻¹`). So the hypotheses are met by
infinitely many labellings, the thesis labelling `g c = 1` among them. -/
theorem geoShared_of_collineations {F : Type*} [Field F] [Fintype F] {α : ℕ} (typ : Fin α → Bool)
    (ε₀ : ZMod 2) (g : Copy α → Equiv.Perm (SPt F ⊕ HLine F))
    (hg : ∀ c, IsAut (incGraph (hexInc (F := F))) (g c)) :
    GeometricShared typ (incGraph (hexInc (F := F))) klass ε₀ g := by
  intro bar k c d _ _
  refine ⟨g d * (g c)⁻¹, fun u v => ?_, fun r _ => by simp⟩
  simp only [Equiv.Perm.mul_apply]
  rw [hg d]
  exact (hg c _ _).symm.trans (by simp)

/-- 3'. Conversely a geometric labelling whose transfers are *not* all trivial exists as soon as the
incidence graph has a non-trivial automorphism; here we only record the general statement. -/
theorem omega3_collineation_labelling {F : Type*} [Field F] [Fintype F] (hq : 8 ≤ Fintype.card F)
    {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ Fintype.card F + 3) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (g : Copy α → Equiv.Perm (SPt F ⊕ HLine F))
    (hg : ∀ c, IsAut (incGraph (hexInc (F := F))) (g c)) (hc : ∀ c u, klass (g c u) = klass u) :
    (9 : ℕ∞) ≤ (omega (incGraph (hexInc (F := F))) klass typ ε₀ (labMk g)).ediam :=
  omega3_hexagon_geometric_shared hq hα h2 typ ε₀ g hc (geoShared_of_collineations typ ε₀ g hg)

/-- 4a. `q = 11`: Gómez's `α = 7`, thesis labelling. -/
theorem q11 : haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    (9 : ℕ∞) ≤ (omega (incGraph (hexInc (F := ZMod 11))) klass (fun _ : Fin 7 => false) 0
      (labMk (fun _ => (1 : Equiv.Perm (SPt (ZMod 11) ⊕ HLine (ZMod 11)))))).ediam := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact omega3_hexagon_thesis (F := ZMod 11) (by simp [ZMod.card]) (α := 7) (by norm_num)
    (by simp [ZMod.card]) _ 0

/-- 4b. `q = 8`: `GF(8)`, Gómez's `α = 5`, thesis labelling, dual reading. -/
theorem q8 : haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    (9 : ℕ∞) ≤ (omega (incGraph (hexInc (F := GaloisField 2 3))) klass (fun _ : Fin 5 => true) 1
      (labMk (fun _ => (1 : Equiv.Perm (SPt (GaloisField 2 3) ⊕ HLine (GaloisField 2 3)))))).ediam := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Fintype (GaloisField 2 3) := Fintype.ofFinite _
  have hc : Fintype.card (GaloisField 2 3) = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]; norm_num
  exact omega3_hexagon_thesis (F := GaloisField 2 3) (by omega) (α := 5) (by norm_num) (by omega) _ 1

#print axioms gomez_alpha
#print axioms geoShared_of_collineations
#print axioms omega3_collineation_labelling
#print axioms q11
#print axioms q8
