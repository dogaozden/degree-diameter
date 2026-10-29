import BipartiteDD.LeanMaxx.Omega45.Geometric7
import BipartiteDD.LeanMaxx.Omega45.Flip

/-!
# `q = 7`: both readings

`Geometric7.lean` proves the far pair for hubs on the colour class `ε₀` of the unbarred hubs. For the dual
reading the hubs on the points are the barred ones, so the hypotheses (Lemmas 4.3 and 4.4) concern the colour
class `ε₀ + 1`. `Flip.lean` exchanges the bars (and the block types) and so reduces this case to the previous
one. `omega45_geometric_of_hyps_points` states the result for both readings: the hypotheses are about the
colour class `p` of the points, and the unbarred hubs sit on either `p` (reading 2) or `p + 1` (dual reading).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open Finset BipartiteDD.LeanMaxx.Omega2 BipartiteDD.LeanMaxx.Omega3

variable {β : Type*} [Fintype β] [DecidableEq β] {B : SimpleGraph β} [DecidableRel B.Adj]
  {κ : β → ZMod 2}

theorem geometric_reindex {α : ℕ} (σ : Copy α ≃ Copy α) {μ : Copy α → Equiv.Perm β}
    (hgeo : Geometric B κ μ) : Geometric B κ (fun c => μ (σ.symm c)) := by
  intro ε c d
  obtain ⟨g, hg, hgr⟩ := hgeo ε (σ.symm c) (σ.symm d)
  exact ⟨g, hg, hgr⟩

/-- **Dual reading** (`q = 7`, modulo Lemmas 4.3 and 4.4 for the colour class `ε₀ + 1` of the barred hubs). -/
theorem omega45_geometric_far_of_hyps_dual [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α)
    (h2 : 2 * α ≤ 7 + 3) (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β)
    (hμ : ∀ c u, κ (μ c u) = κ u) (hgeo : Geometric B κ μ)
    (hP : PerpBound B κ (ε₀ + 1) 4144) (hB : Bonferroni B κ (ε₀ + 1) 4 140) :
    ∃ x y, (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).edist x y := by
  have hflip := omega45_geometric_far_of_hyps H hα h2 (flipTyp typ) (ε₀ + 1)
    (fun c => μ ((sigma typ).symm c)) (fun c u => hμ _ u) (geometric_reindex (sigma typ) hgeo) hP hB
  refine exists_far_of_hom (flipV typ) (fun hxy => ?_) flipV_surj hflip
  exact flipV_adj (mk := labMk μ) (mk' := labMk fun c => μ ((sigma typ).symm c))
    (fun bar c u => by simp [labMk]) hxy

/-- **Theorem 4.5 for both readings (`q = 7`, modulo Lemmas 4.3 and 4.4 for the colour class `p` of the
points).** -/
theorem omega45_geometric_of_hyps_points [Nonempty β] (H : Hex B κ 7) {α : ℕ} (hα : 0 < α)
    (h2 : 2 * α ≤ 7 + 3) (typ : Fin α → Bool) (p ε₀ : ZMod 2) (hε : ε₀ = p ∨ ε₀ + 1 = p)
    (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u) (hgeo : Geometric B κ μ)
    (hP : PerpBound B κ p 4144) (hB : Bonferroni B κ p 4 140) :
    (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).ediam := by
  rcases hε with rfl | rfl
  · exact omega45_geometric_of_hyps H hα h2 typ _ μ hμ hgeo hP hB
  · obtain ⟨x, y, h⟩ := omega45_geometric_far_of_hyps_dual H hα h2 typ ε₀ μ hμ hgeo hP hB
    exact h.trans SimpleGraph.edist_le_ediam

end BipartiteDD.LeanMaxx.Omega45
