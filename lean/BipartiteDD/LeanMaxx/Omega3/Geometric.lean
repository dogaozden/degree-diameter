import BipartiteDD.LeanMaxx.Omega3.Main

/-!
# Geometric labellings (Lemma 1.1 and the statement of Theorem 3.3)

A *labelling* of the copies is a family `μ c : Perm β` (`c : Copy α`) of colour-preserving bijections: the
row `r` of a hub is joined to the vertex `μ c r` of copy `c` (the same bijection `μ c` serves the points and
the lines of copy `c`, and both hub classes of a colour that meet `c`). The graph is
`omega B κ typ ε₀ (labMk μ)`.

`Geometric B κ μ` says that every transfer map is the restriction of an automorphism of the incidence graph:
for each colour `ε` and copies `c, d` there is a graph automorphism `g` of `B` with `μ d r = g (μ c r)` for
every row `r` of colour `ε` (a collineation, or a duality when it exists; `g` is forced to preserve colours).

`omega3_geometric`: for `q ≥ 8`, every geometric labelling gives diameter `≥ 9`. The proof maps the graph
homomorphically to the normal form of Lemma 1.1 (apply `a_c⁻¹` to copy `c`), where `omega3_ediam` applies.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset BipartiteDD.LeanMaxx.Omega2

variable {β : Type*} {α : ℕ}

/-- The marks of a labelling `μ`: both hub colours use the same bijection of each copy. -/
def labMk (μ : Copy α → Equiv.Perm β) : Bool → Copy α → Equiv.Perm β := fun _ c => μ c

/-- A graph automorphism (not necessarily colour-preserving). -/
def IsAut (B : SimpleGraph β) (g : Equiv.Perm β) : Prop := ∀ u v, B.Adj (g u) (g v) ↔ B.Adj u v

/-- **Geometric labelling**: every transfer map is the restriction of an automorphism of the incidence graph. -/
def Geometric (B : SimpleGraph β) (κ : β → ZMod 2) (μ : Copy α → Equiv.Perm β) : Prop :=
  ∀ (ε : ZMod 2) (c d : Copy α), ∃ g : Equiv.Perm β, IsAut B g ∧ ∀ r, κ r = ε → μ d r = g (μ c r)

variable {B : SimpleGraph β} {κ : β → ZMod 2} {q : ℕ}

theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

theorem zmod2_sum_eq (a b c d : ZMod 2) (h1 : a ≠ b) (h2 : c ≠ d) : a + c = b + d := by
  revert h1 h2; revert a b c d; decide

/-- An automorphism of a connected bipartite graph that maps one vertex to a vertex of the same colour
preserves all colours. -/
theorem aut_col [Fintype β] [DecidableEq β] [DecidableRel B.Adj] (H : Hex B κ q) {g : Equiv.Perm β} (hg : IsAut B g)
    {r : β} (hr : κ (g r) = κ r) (u : β) : κ (g u) = κ u := by
  obtain ⟨W⟩ := H.reach r u
  have key : ∀ {x y : β} (W : B.Walk x y), κ (g x) + κ x = κ (g y) + κ y := by
    intro x y W
    induction W with
    | nil => rfl
    | @cons a b c hab W ih =>
      rw [zmod2_sum_eq (κ (g a)) (κ (g b)) (κ a) (κ b) (H.col _ _ ((hg a b).2 hab)) (H.col a b hab)]
      exact ih
  have := key W
  have h0 : κ (g r) + κ r = 0 := by rw [hr]; exact zmod2_add_self _
  rw [h0] at this
  have h3 : κ (g u) + κ u = 0 := this.symm
  revert h3; generalize κ (g u) = a; generalize κ u = b; revert a b; decide

/-- Colour-preserving automorphisms are elements of `autSub`. -/
theorem mem_autSub {g : Equiv.Perm β} (hg : IsAut B g) (hc : ∀ u, κ (g u) = κ u) : g ∈ autSub B κ := ⟨hg, hc⟩

section Reduce

variable (κ) {ε₀ : ZMod 2}

/-- Apply `(a c)⁻¹` to copy `c` and rename the rows by `μ₀`: the map to the normal form. -/
def Phi (a : Copy α → Equiv.Perm β) (μ₀ : Equiv.Perm β) (hμ₀ : ∀ u, κ (μ₀ u) = κ u) :
    Vtx α κ ε₀ → Vtx α κ ε₀
  | Sum.inl (c, y) => Sum.inl (c, (a c)⁻¹ y)
  | Sum.inr h => Sum.inr ⟨h.bar, h.k, μ₀ h.r, by rw [hμ₀]; exact h.hr⟩

/-- The inverse of `Phi`. -/
def Psi (a : Copy α → Equiv.Perm β) (μ₀ : Equiv.Perm β) (hμ₀ : ∀ u, κ (μ₀ u) = κ u) :
    Vtx α κ ε₀ → Vtx α κ ε₀
  | Sum.inl (c, y) => Sum.inl (c, a c y)
  | Sum.inr h => Sum.inr ⟨h.bar, h.k, μ₀⁻¹ h.r, by
      have := hμ₀ (μ₀⁻¹ h.r)
      rw [show μ₀ (μ₀⁻¹ h.r) = h.r from by simp] at this
      rw [← this]; exact h.hr⟩

variable {κ}

theorem Phi_Psi (a : Copy α → Equiv.Perm β) (μ₀ : Equiv.Perm β) (hμ₀ : ∀ u, κ (μ₀ u) = κ u)
    (x : Vtx α κ ε₀) : Phi κ a μ₀ hμ₀ (Psi κ a μ₀ hμ₀ x) = x := by
  rcases x with ⟨c, y⟩ | h
  · simp [Phi, Psi]
  · simp [Phi, Psi]

variable {typ : Fin α → Bool}

/-- `Phi` is a graph homomorphism from the graph of the labelling `μ` to the normal-form graph. -/
theorem Phi_adj (μ lam' a b : Copy α → Equiv.Perm β) (c₀ : Copy α) (hμ : ∀ c u, κ (μ c u) = κ u)
    (ha : ∀ c, IsAut B (a c)) (hlam : ∀ c, lam' c = (a c)⁻¹ * b c)
    (haμ : ∀ c r, κ r = ε₀ → μ c r = a c (μ c₀ r))
    (hbμ : ∀ c r, κ r = ε₀ + 1 → μ c r = b c (μ c₀ r))
    {x y : Vtx α κ ε₀} (hxy : (omega B κ typ ε₀ (labMk μ)).Adj x y) :
    (omega B κ typ ε₀ (nfmk lam')).Adj (Phi κ a (μ c₀) (hμ c₀) x) (Phi κ a (μ c₀) (hμ c₀) y) := by
  have key : ∀ (h : Hub κ ε₀) (c : Copy α) (y : β),
      (omega B κ typ ε₀ (labMk μ)).Adj (Sum.inr h) (Sum.inl (c, y)) →
      (omega B κ typ ε₀ (nfmk lam')).Adj (Phi κ a (μ c₀) (hμ c₀) (Sum.inr h)) (Phi κ a (μ c₀) (hμ c₀) (Sum.inl (c, y))) := by
    intro h c y hadj
    rw [omega_adj_hc] at hadj
    simp only [Phi]
    rw [omega_adj_hc]
    refine ⟨hadj.1, ?_⟩
    obtain ⟨bar, k, r, hr⟩ := h
    simp only [labMk] at hadj
    rw [hadj.2]
    cases bar
    · simp only [nfmk, hubcol_false] at hr ⊢
      rw [haμ c r hr]; simp
    · simp only [nfmk, hubcol_true] at hr ⊢
      rw [hbμ c r hr, hlam]; simp
  rcases x with ⟨c, z⟩ | h <;> rcases y with ⟨c', z'⟩ | h'
  · rw [omega_adj_cc] at hxy
    obtain ⟨rfl, hadj⟩ := hxy
    simp only [Phi]
    rw [omega_adj_cc]
    refine ⟨rfl, ?_⟩
    rw [← (ha c) _ _]; simpa using hadj
  · rw [SimpleGraph.adj_comm]
    rw [SimpleGraph.adj_comm] at hxy
    exact key h' c z hxy
  · exact key h c' z' hxy
  · exact absurd hxy not_omega_adj_hh

end Reduce

section Main

variable [Fintype β] [DecidableEq β] [DecidableRel B.Adj] [Nonempty β]

/-- **Theorem 3.3 for geometric labellings.** Let `H` be a generalized hexagon of order `(q, q)`, `q ≥ 8`,
`α ≥ 1` blocks with `2 α ≤ q + 3` and any block types. For every colour-preserving labelling `μ` of the
copies in which every transfer map is induced by an automorphism of the incidence graph, `ΩH_q` has
diameter at least `9`. The colour `ε₀` of the unbarred hubs is arbitrary (`0`: reading 2; `1`: the dual). -/
theorem omega3_geometric (H : Hex B κ q) (hq : 8 ≤ q) (hα : 0 < α) (h2 : 2 * α ≤ q + 3)
    (typ : Fin α → Bool) (ε₀ : ZMod 2) (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : Geometric B κ μ) :
    (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).ediam := by
  classical
  set c₀ : Copy α := (⟨0, hα⟩, 0) with hc₀
  -- the transfer automorphisms from the base copy `c₀`
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
  obtain ⟨x₂, y₂, h₂⟩ := omega3_far H hq hα h2 typ ε₀ lam
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
  exact hedist.trans SimpleGraph.edist_le_ediam

end Main

end BipartiteDD.LeanMaxx.Omega3
