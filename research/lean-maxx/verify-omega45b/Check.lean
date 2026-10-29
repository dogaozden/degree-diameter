import BipartiteDD.LeanMaxx.Omega45b.Axioms
open BipartiteDD BipartiteDD.Hexagon BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45 BipartiteDD.LeanMaxx.Omega45b

-- the headline statements as elaborated
#check @bonferroni_of_hex
#check @omega45_H7_geometric
#check @omega45_H7_of_perpBound
#print Lemma44
#check @perpBound_of_lemma44
#print Bonferroni
#print PerpBound
#print Geometric

-- Lemma44 is a plain definition, not an axiom: no axiom of that name; the theorem depends only on standard axioms
#print axioms bonferroni_of_hex
#print axioms omega45_H7_geometric
#print axioms omega45_H7_of_perpBound
#print axioms perpBound_of_lemma44

-- the statement is not vacuous: the identity labelling (all lambda = 1) satisfies its hypotheses
example {α : ℕ} : ∃ μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7),
    (∀ c u, klass (μ c u) = klass u) ∧ Geometric G7 klass μ := by
  refine ⟨fun _ => 1, fun c u => rfl, ?_⟩
  intro ε c d
  exact ⟨1, fun u v => Iff.rfl, fun r _ => rfl⟩

-- Bonferroni (k=4) is implied by the note's k=6 form (bonferroni_mono)
example {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj] {κ : β → ZMod 2} {ε₀ : ZMod 2}
    (h : Bonferroni B κ ε₀ 6 140) : Bonferroni B κ ε₀ 4 140 := bonferroni_mono (by norm_num) h

-- Theorem 4.5 at H(7) with the note's definition of a geometric labelling (transfers along shared hub classes),
-- obtained by composing the Lean headline with Omega3's `geometric_of_shared`: still only Lemma44 as a hypothesis.
theorem omega45_H7_geometric_shared_check (hL : Lemma44) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm (SPt F7 ⊕ HLine F7))
    (hμ : ∀ c u, klass (μ c u) = klass u) (hgeo : GeometricShared typ G7 klass ε₀ μ) :
    (9 : ℕ∞) ≤ (omega G7 klass typ ε₀ (labMk μ)).ediam :=
  omega45_H7_geometric hL hα h2 typ ε₀ μ hμ (geometric_of_shared μ hgeo)
#print axioms omega45_H7_geometric_shared_check
