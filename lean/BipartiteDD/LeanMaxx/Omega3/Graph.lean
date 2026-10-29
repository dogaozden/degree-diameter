import BipartiteDD.LeanMaxx.Omega3.Wiring

/-!
# The graph `ΩH_q` for a labelling of the copies

`β` is the vertex type of the incidence graph `B` of a generalized hexagon, `κ` its proper 2-colouring.
The graph `omega B typ ε₀ mk` has

* copy vertices `(c, y)`, `c : Copy α` a copy, `y : β`, joined inside a copy as in `B`;
* hub vertices `(bar, k, r)` with `r : β` a row of colour `hubcol ε₀ bar` (unbarred hubs have colour `ε₀`,
  barred hubs `ε₀ + 1`; `ε₀ = 0` is reading 2 of the note, `ε₀ = 1` its point/line dual).

Hub `(bar, k, r)` is joined to the mark `mk bar c r` in every copy `c` met by the class `(bar, k)`
(`meets typ bar k c`). A *labelling* is the family `mk bar c : Perm β` of colour-preserving bijections
(row ↦ mark). In the normal form of Lemma 1.1, `mk false c = 1` and `mk true c = λ_c`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset

/-- The colour of the rows of hub class `bar`. -/
def hubcol (ε₀ : ZMod 2) (bar : Bool) : ZMod 2 := if bar then ε₀ + 1 else ε₀

@[simp] theorem hubcol_false (ε₀ : ZMod 2) : hubcol ε₀ false = ε₀ := rfl
@[simp] theorem hubcol_true (ε₀ : ZMod 2) : hubcol ε₀ true = ε₀ + 1 := rfl

theorem hubcol_inj (ε₀ : ZMod 2) {b b' : Bool} (h : hubcol ε₀ b = hubcol ε₀ b') : b = b' := by
  revert h; revert ε₀ b b'; decide

/-- The colour-preserving automorphisms of `B`, as permutations of the vertex set. -/
def autSub {β : Type*} (B : SimpleGraph β) (κ : β → ZMod 2) : Subgroup (Equiv.Perm β) where
  carrier := {f | (∀ u v, B.Adj (f u) (f v) ↔ B.Adj u v) ∧ ∀ u, κ (f u) = κ u}
  mul_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun u v => ?_, fun u => ?_⟩
    · simp only [Equiv.Perm.mul_apply]; rw [hf1, hg1]
    · simp only [Equiv.Perm.mul_apply]; rw [hf2, hg2]
  one_mem' := ⟨fun _ _ => Iff.rfl, fun _ => rfl⟩
  inv_mem' := by
    rintro f ⟨hf1, hf2⟩
    refine ⟨fun u v => ?_, fun u => ?_⟩
    · rw [← hf1 (f⁻¹ u) (f⁻¹ v)]; simp
    · have := hf2 (f⁻¹ u); simp at this; exact this.symm

variable {β : Type*} {α : ℕ}

/-- A hub vertex: a class `(bar, k)` and a row `r` of the right colour. -/
structure Hub (κ : β → ZMod 2) (ε₀ : ZMod 2) where
  bar : Bool
  k : ZMod 5
  r : β
  hr : κ r = hubcol ε₀ bar

/-- Vertices of `ΩH_q`: copy vertices and hubs. -/
abbrev Vtx (α : ℕ) (κ : β → ZMod 2) (ε₀ : ZMod 2) := (Copy α × β) ⊕ Hub κ ε₀

section Def

variable (B : SimpleGraph β) (κ : β → ZMod 2) (typ : Fin α → Bool) (ε₀ : ZMod 2)
  (mk : Bool → Copy α → Equiv.Perm β)

/-- The generating relation of the edges. -/
def omegaRel : Vtx α κ ε₀ → Vtx α κ ε₀ → Prop
  | Sum.inl (c, y), Sum.inl (c', y') => c = c' ∧ B.Adj y y'
  | Sum.inr h, Sum.inl (c, y) => meets typ h.bar h.k c = true ∧ y = mk h.bar c h.r
  | _, _ => False

/-- **The graph `ΩH_q`** with the labelling `mk`. -/
def omega : SimpleGraph (Vtx α κ ε₀) := SimpleGraph.fromRel (omegaRel B κ typ ε₀ mk)

variable {B κ typ ε₀ mk}

theorem omega_adj_cc {c c' : Copy α} {y y' : β} :
    (omega B κ typ ε₀ mk).Adj (Sum.inl (c, y)) (Sum.inl (c', y')) ↔ c = c' ∧ B.Adj y y' := by
  simp only [omega, SimpleGraph.fromRel_adj, omegaRel]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩
  · rintro ⟨rfl, h⟩
    exact ⟨fun e => h.ne (by simpa using e), Or.inl ⟨rfl, h⟩⟩

theorem omega_adj_hc {h : Hub κ ε₀} {c : Copy α} {y : β} :
    (omega B κ typ ε₀ mk).Adj (Sum.inr h) (Sum.inl (c, y)) ↔
      meets typ h.bar h.k c = true ∧ y = mk h.bar c h.r := by
  simp only [omega, SimpleGraph.fromRel_adj, omegaRel]
  constructor
  · rintro ⟨_, h | h⟩
    · exact h
    · exact h.elim
  · intro h; exact ⟨by simp, Or.inl h⟩

theorem omega_adj_ch {h : Hub κ ε₀} {c : Copy α} {y : β} :
    (omega B κ typ ε₀ mk).Adj (Sum.inl (c, y)) (Sum.inr h) ↔
      meets typ h.bar h.k c = true ∧ y = mk h.bar c h.r := by
  rw [SimpleGraph.adj_comm]; exact omega_adj_hc

theorem not_omega_adj_hh {h h' : Hub κ ε₀} : ¬ (omega B κ typ ε₀ mk).Adj (Sum.inr h) (Sum.inr h') := by
  simp [omega, SimpleGraph.fromRel_adj, omegaRel]

/-- The 2-colouring of `ΩH_q`. -/
def Kcol : Vtx α κ ε₀ → ZMod 2 := Sum.elim (fun p => κ p.2) (fun h => κ h.r + 1)

theorem Kcol_proper (hκ : ∀ u v, B.Adj u v → κ u ≠ κ v) (hmk : ∀ bar c u, κ (mk bar c u) = κ u)
    {a b : Vtx α κ ε₀} (hab : (omega B κ typ ε₀ mk).Adj a b) : Kcol a ≠ Kcol b := by
  rcases a with ⟨c, y⟩ | h <;> rcases b with ⟨c', y'⟩ | h'
  · rw [omega_adj_cc] at hab
    simpa [Kcol] using hκ _ _ hab.2
  · rw [omega_adj_ch] at hab
    simp only [Kcol, Sum.elim_inl, Sum.elim_inr]
    rw [hab.2, hmk]
    intro e
    have : (κ h'.r : ZMod 2) = κ h'.r + 1 := e
    revert this; generalize κ h'.r = s; revert s; decide
  · rw [omega_adj_hc] at hab
    simp only [Kcol, Sum.elim_inl, Sum.elim_inr]
    rw [hab.2, hmk]
    intro e
    have : κ h.r + 1 = κ h.r := e
    revert this; generalize κ h.r = s; revert s; decide
  · exact (not_omega_adj_hh hab).elim

end Def

end BipartiteDD.LeanMaxx.Omega3
