import BipartiteDD.LeanMaxx.Omega45.Q7
import BipartiteDD.LeanMaxx.Omega3.Shared

/-!
# From twisted to geometric labellings, at `q = 7`

`Omega3/Geometric.lean` reduces a geometric labelling to the normal form of Lemma 1.1 and then applies
`omega3_far` (which needs `q ≥ 8`). The reduction itself works for any far-pair statement in the normal form,
so here it is restated with that statement as a hypothesis (`geometric_far_of_nf`) and applied to the `q = 7`
results of `Q7.lean`:

* `omega45_geometric_alpha_le_four` (unconditional): `q = 7`, `α ≤ 4`, every geometric labelling.
* `omega45_geometric_of_hyps` (Theorem 4.5, modulo Lemmas 4.3 and 4.4): `q = 7`, `α ≤ 5`, every geometric labelling.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open Finset BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2} {q α : ℕ}

/-- The reduction of `Omega3.omega3_geometric`, with the normal-form far pair as a hypothesis. -/
theorem geometric_far_of_nf [Nonempty β] (H : Hex B κ q) (hα : 0 < α) (typ : Fin α → Bool) (ε₀ : ZMod 2)
    (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u) (hgeo : Geometric B κ μ)
    (hnf : ∀ lam : Copy α → autSub B κ, ∃ x y, (9 : ℕ∞) ≤
      (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist x y) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).edist x y := by
  classical
  set c₀ : Copy α := (⟨0, hα⟩, 0) with hc₀
  have hT : ∀ (ε : ZMod 2) (c : Copy α), ∃ g : Equiv.Perm β, g ∈ autSub B κ ∧ ∀ r, κ r = ε → μ c r = g (μ c₀ r) := by
    intro ε c
    obtain ⟨g, hg, hgr⟩ := hgeo ε c₀ c
    obtain ⟨r, hr⟩ := exists_row H ε
    refine ⟨g, mem_autSub hg (aut_col H hg (r := μ c₀ r) ?_), hgr⟩
    rw [← hgr r hr, hμ, hμ, hr]
  choose a ha haμ using hT ε₀
  choose b hb hbμ using hT (ε₀ + 1)
  let lam : Copy α → autSub B κ := fun c =>
    ⟨(a c)⁻¹ * b c, (autSub B κ).mul_mem ((autSub B κ).inv_mem (ha c)) (hb c)⟩
  obtain ⟨x₂, y₂, h₂⟩ := hnf lam
  have hΦ : ∀ {x y : Vtx α κ ε₀}, (omega B κ typ ε₀ (labMk μ)).Adj x y →
      (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).Adj (Phi κ a (μ c₀) (hμ c₀) x)
        (Phi κ a (μ c₀) (hμ c₀) y) := fun hxy =>
    Phi_adj (typ := typ) (ε₀ := ε₀) μ (fun c => (lam c : Equiv.Perm β)) a b c₀ hμ
      (fun c => (ha c).1) (fun c => rfl) haμ hbμ hxy
  have hedist : (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).edist
      (Psi κ a (μ c₀) (hμ c₀) x₂) (Psi κ a (μ c₀) (hμ c₀) y₂) := by
    unfold SimpleGraph.edist
    refine le_iInf fun W => ?_
    have hW := SimpleGraph.edist_le (W.map ⟨Phi κ a (μ c₀) (hμ c₀), hΦ⟩)
    rw [SimpleGraph.Walk.length_map] at hW
    change (omega B κ typ ε₀ (nfmk (fun c => (lam c : Equiv.Perm β)))).edist
      (Phi κ a (μ c₀) (hμ c₀) (Psi κ a (μ c₀) (hμ c₀) x₂))
      (Phi κ a (μ c₀) (hμ c₀) (Psi κ a (μ c₀) (hμ c₀) y₂)) ≤ _ at hW
    rw [Phi_Psi, Phi_Psi] at hW
    exact h₂.trans hW
  exact ⟨_, _, hedist⟩

/-- `q = 7`, at most four blocks: every geometric labelling has a far pair (two vertices at distance `≥ 9`). -/
theorem omega45_geometric_far_alpha_le_four [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (hα4 : α ≤ 4)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : Geometric B κ μ) : ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).edist x y :=
  geometric_far_of_nf H hα typ ε₀ μ hμ hgeo fun lam => omega45_alpha_le_four H hα hα4 typ ε₀ lam

theorem omega45_geometric_alpha_le_four [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (hα4 : α ≤ 4)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : Geometric B κ μ) : (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).ediam := by
  obtain ⟨x, y, h⟩ := omega45_geometric_far_alpha_le_four H hα hα4 typ ε₀ μ hμ hgeo
  exact h.trans SimpleGraph.edist_le_ediam

/-- `q = 7`, Theorem 4.5 modulo Lemmas 4.3 and 4.4: every geometric labelling gives diameter `≥ 9`. -/
theorem omega45_geometric_far_of_hyps [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : Geometric B κ μ) (hP : PerpBound B κ ε₀ 4144) (hB : Bonferroni B κ ε₀ 4 140) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).edist x y :=
  geometric_far_of_nf H hα typ ε₀ μ hμ hgeo fun lam => omega45_of_hyps H hα h2 typ lam hP hB

theorem omega45_geometric_of_hyps [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : Geometric B κ μ) (hP : PerpBound B κ ε₀ 4144) (hB : Bonferroni B κ ε₀ 4 140) :
    (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).ediam := by
  obtain ⟨x, y, h⟩ := omega45_geometric_far_of_hyps H hα h2 typ ε₀ μ hμ hgeo hP hB
  exact h.trans SimpleGraph.edist_le_ediam

end BipartiteDD.LeanMaxx.Omega45
