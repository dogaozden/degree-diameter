import BipartiteDD.LeanMaxx.Omega3.Geometric

/-!
# Geometric labellings, in the wording of the note

The note calls a labelling *geometric* if every transfer map `T_Y(c → d)` of a hub class `Y` that meets the
copies `c` and `d` is the restriction of an automorphism of the incidence graph. `GeometricShared` is exactly
that. Because any two copies are linked by a chain of copies, consecutive ones sharing a hub class of the
colour, and transfers compose, it implies `Geometric` (`geometric_of_shared`); hence
`omega3_geometric_shared` and `omega3_hexagon_geometric_shared`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega3

open Finset

variable {β : Type*} {α : ℕ}

/-! ### Connectivity of the sharing relation -/

/-- Within a block, a hub class links positions differing by a fixed nonzero step `d`. -/
theorem step_exists : ∀ ty bar : Bool, ∃ d : ZMod 5, d ≠ 0 ∧ ∀ i : ZMod 5,
    ∃ k : ZMod 5, metPos ty bar k i = true ∧ metPos ty bar k (i + d) = true := by
  decide

theorem mul_surj : ∀ d : ZMod 5, d ≠ 0 → ∀ x : ZMod 5, ∃ n : Fin 5, x = (n : ℕ) * d := by
  decide

/-- Within one block all five positions are linked. -/
theorem pos_connected (ty bar : Bool) (i j : ZMod 5) :
    Relation.ReflTransGen (fun i j : ZMod 5 => ∃ k, metPos ty bar k i = true ∧ metPos ty bar k j = true) i j := by
  obtain ⟨d, hd, hstep⟩ := step_exists ty bar
  obtain ⟨n, hn⟩ := mul_surj d hd (j - i)
  have key : ∀ m : ℕ, Relation.ReflTransGen
      (fun i j : ZMod 5 => ∃ k, metPos ty bar k i = true ∧ metPos ty bar k j = true) i (i + m * d) := by
    intro m
    induction m with
    | zero => simpa using Relation.ReflTransGen.refl
    | succ m ih =>
      refine ih.tail ?_
      obtain ⟨k, hk1, hk2⟩ := hstep (i + m * d)
      refine ⟨k, hk1, ?_⟩
      have : i + ((m + 1 : ℕ) : ZMod 5) * d = i + m * d + d := by push_cast; ring
      rw [this]; exact hk2
  have := key n
  rwa [← hn, add_sub_cancel] at this

variable (typ : Fin α → Bool)

/-- Any two copies are linked by a chain of copies, consecutive ones sharing a hub class of colour `bar`. -/
theorem copy_connected (bar : Bool) (c d : Copy α) :
    Relation.ReflTransGen (fun c d : Copy α => ∃ k, meets typ bar k c = true ∧ meets typ bar k d = true) c d := by
  obtain ⟨b, i⟩ := c
  obtain ⟨b', j'⟩ := d
  -- a class through `(b, i)` also meets some position `j` of block `b'`
  have hk : ∃ k : ZMod 5, metPos (typ b) bar k i = true := by
    have h := BipartiteDD.LeanMaxx.Omega3.card_cls (typ b) bar i
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (by omega : 0 < ((univ : Finset (ZMod 5)).filter
      fun k => metPos (typ b) bar k i = true).card)
    exact ⟨k, (Finset.mem_filter.1 hk).2⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨j, hj⟩ : ∃ j : ZMod 5, metPos (typ b') bar k j = true := by
    have h := BipartiteDD.LeanMaxx.Omega3.card_pos (typ b') bar k
    obtain ⟨j, hj⟩ := Finset.card_pos.1 (by omega : 0 < ((univ : Finset (ZMod 5)).filter
      fun i => metPos (typ b') bar k i = true).card)
    exact ⟨j, (Finset.mem_filter.1 hj).2⟩
  have h1 : Relation.ReflTransGen (fun c d : Copy α => ∃ k, meets typ bar k c = true ∧ meets typ bar k d = true)
      (b, i) (b', j) := Relation.ReflTransGen.single ⟨k, hk, hj⟩
  have h2 : Relation.ReflTransGen (fun c d : Copy α => ∃ k, meets typ bar k c = true ∧ meets typ bar k d = true)
      (b', j) (b', j') := by
    have := pos_connected (typ b') bar j j'
    exact Relation.ReflTransGen.lift (fun i : ZMod 5 => ((b', i) : Copy α)) (fun x y h => h) j j' this
  exact h1.trans h2

/-! ### Transfers along shared classes -/

variable (B : SimpleGraph β) (κ : β → ZMod 2) (ε₀ : ZMod 2)

/-- **Geometric labelling, as in the note**: for every hub class `(bar, k)` meeting copies `c` and `d`, the
transfer `T(c → d)` (row `r ↦` its mark in `d` after its mark in `c`) is the restriction of an automorphism
of the incidence graph. -/
def GeometricShared (μ : Copy α → Equiv.Perm β) : Prop :=
  ∀ (bar : Bool) (k : ZMod 5) (c d : Copy α), meets typ bar k c = true → meets typ bar k d = true →
    ∃ g : Equiv.Perm β, IsAut B g ∧ ∀ r, κ r = hubcol ε₀ bar → μ d r = g (μ c r)

variable {B κ ε₀ typ}

theorem hubcol_surj : ∀ ε₀ ε : ZMod 2, ∃ bar : Bool, hubcol ε₀ bar = ε := by decide

theorem geometric_of_shared (μ : Copy α → Equiv.Perm β) (h : GeometricShared typ B κ ε₀ μ) :
    Geometric B κ μ := by
  intro ε c d
  obtain ⟨bar, rfl⟩ := hubcol_surj ε₀ ε
  have key : ∀ c d : Copy α, Relation.ReflTransGen
      (fun c d : Copy α => ∃ k, meets typ bar k c = true ∧ meets typ bar k d = true) c d →
      ∃ g : Equiv.Perm β, IsAut B g ∧ ∀ r, κ r = hubcol ε₀ bar → μ d r = g (μ c r) := by
    intro c d hcd
    induction hcd with
    | refl => exact ⟨1, fun _ _ => Iff.rfl, fun r _ => rfl⟩
    | @tail d e _ hde ih =>
      obtain ⟨g, hg, hgr⟩ := ih
      obtain ⟨k, hk1, hk2⟩ := hde
      obtain ⟨g', hg', hgr'⟩ := h bar k d e hk1 hk2
      refine ⟨g' * g, fun u v => ?_, fun r hr => ?_⟩
      · simp only [Equiv.Perm.mul_apply]; rw [hg', hg]
      · simp only [Equiv.Perm.mul_apply]; rw [hgr' r hr, hgr r hr]
  exact key c d (copy_connected typ bar c d)

section Final

variable [Fintype β] [DecidableEq β] [DecidableRel B.Adj] [Nonempty β] {q : ℕ}

/-- **Theorem 3.3 (abstract, in the wording of the note).** -/
theorem omega3_geometric_shared (H : Hex B κ q) (hq : 8 ≤ q) (hα : 0 < α) (h2 : 2 * α ≤ q + 3)
    (μ : Copy α → Equiv.Perm β) (hμ : ∀ c u, κ (μ c u) = κ u)
    (hgeo : GeometricShared typ B κ ε₀ μ) :
    (9 : ℕ∞) ≤ (omega B κ typ ε₀ (labMk μ)).ediam :=
  omega3_geometric H hq hα h2 typ ε₀ μ hμ (geometric_of_shared μ hgeo)

end Final

end BipartiteDD.LeanMaxx.Omega3
