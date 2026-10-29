import BipartiteDD.LeanMaxx.Omega3.Geometric

/-!
# Exchanging the two hub bars (the dual reading)

The wiring of `ΩH_q` with block types `typ` and unbarred hubs on colour `ε₀` is isomorphic (as far as far pairs
go) to the wiring with the types exchanged (`flipTyp typ`), the bars exchanged and unbarred hubs on colour
`ε₀ + 1`: rotate the positions of the copies of a block of type a by `0` and of a block of type b by `-1`, and
shift the class index of a barred hub by `-1`. This is `metPos_flip`, a finite check. It lets `q = 7` results
proved for hubs on one colour (the unbarred hubs) be used for the barred hubs, that is, for the dual reading.

* `flipV`: the vertex map `ΩH(typ, ε₀, mk) → ΩH(flipTyp typ, ε₀ + 1, mk')`, where
  `mk' (!bar) (σ c) = mk bar c`;
* `flipV_adj`: it preserves adjacency; `flipV_surj`: it is onto;
* `exists_far_of_hom`: a far pair downstairs gives one upstairs.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace BipartiteDD.LeanMaxx.Omega45

open Finset BipartiteDD.LeanMaxx.Omega3

/-- Position shift of a block: `0` for type a, `-1` for type b. -/
def sh (ty : Bool) : ZMod 5 := if ty then -1 else 0

/-- Class shift of a hub: `-1` for barred hubs, `0` for unbarred ones. -/
def dl (bar : Bool) : ZMod 5 := if bar then -1 else 0

theorem metPos_flip : ∀ ty bar : Bool, ∀ k i : ZMod 5,
    metPos ty bar k i = metPos (!ty) (!bar) (k + dl bar) (i + sh ty) := by
  decide

variable {β : Type*} {α : ℕ}

/-- The rotation of the positions of each block. -/
def sigma (typ : Fin α → Bool) : Copy α ≃ Copy α where
  toFun c := (c.1, c.2 + sh (typ c.1))
  invFun c := (c.1, c.2 - sh (typ c.1))
  left_inv c := by simp
  right_inv c := by simp

/-- The block types with a and b exchanged. -/
def flipTyp (typ : Fin α → Bool) : Fin α → Bool := fun b => !typ b

theorem meets_flip (typ : Fin α → Bool) (bar : Bool) (k : ZMod 5) (c : Copy α) :
    meets (flipTyp typ) (!bar) (k + dl bar) (sigma typ c) = meets typ bar k c := by
  simp only [meets, flipTyp, sigma, Equiv.coe_fn_mk]
  rw [metPos_flip (typ c.1) bar k c.2]

variable {κ : β → ZMod 2} {ε₀ : ZMod 2}

theorem hubcol_flip (bar : Bool) : hubcol (ε₀ + 1) (!bar) = hubcol ε₀ bar := by
  cases bar <;> simp [hubcol] <;> revert ε₀ <;> decide

/-- The hub with the bar exchanged. -/
def flipHub (h : Hub κ ε₀) : Hub κ (ε₀ + 1) :=
  ⟨!h.bar, h.k + dl h.bar, h.r, by rw [hubcol_flip]; exact h.hr⟩

/-- The vertex map of the exchange. -/
def flipV (typ : Fin α → Bool) : Vtx α κ ε₀ → Vtx α κ (ε₀ + 1)
  | Sum.inl (c, y) => Sum.inl (sigma typ c, y)
  | Sum.inr h => Sum.inr (flipHub h)

variable {B : SimpleGraph β} {typ : Fin α → Bool} {mk mk' : Bool → Copy α → Equiv.Perm β}

theorem flipV_adj (hmk : ∀ bar c u, mk' (!bar) (sigma typ c) u = mk bar c u)
    {x y : Vtx α κ ε₀} (hxy : (omega B κ typ ε₀ mk).Adj x y) :
    (omega B κ (flipTyp typ) (ε₀ + 1) mk').Adj (flipV typ x) (flipV typ y) := by
  have key : ∀ (h : Hub κ ε₀) (c : Copy α) (y : β),
      (omega B κ typ ε₀ mk).Adj (Sum.inr h) (Sum.inl (c, y)) →
      (omega B κ (flipTyp typ) (ε₀ + 1) mk').Adj (flipV typ (Sum.inr h)) (flipV typ (Sum.inl (c, y))) := by
    intro h c y hadj
    rw [omega_adj_hc] at hadj
    simp only [flipV, flipHub]
    rw [omega_adj_hc]
    refine ⟨?_, ?_⟩
    · simp only
      rw [meets_flip]; exact hadj.1
    · simp only
      rw [hmk, hadj.2]
  rcases x with ⟨c, z⟩ | h <;> rcases y with ⟨c', z'⟩ | h'
  · rw [omega_adj_cc] at hxy
    obtain ⟨rfl, hadj⟩ := hxy
    simp only [flipV]
    rw [omega_adj_cc]
    exact ⟨rfl, hadj⟩
  · rw [SimpleGraph.adj_comm]
    rw [SimpleGraph.adj_comm] at hxy
    exact key h' c z hxy
  · exact key h c' z' hxy
  · exact absurd hxy not_omega_adj_hh

theorem flipV_surj : Function.Surjective (flipV (κ := κ) (ε₀ := ε₀) typ) := by
  rintro (⟨c, y⟩ | ⟨bar', k', r, hr⟩)
  · exact ⟨Sum.inl ((sigma typ).symm c, y), by simp [flipV]⟩
  · refine ⟨Sum.inr ⟨!bar', k' - dl (!bar'), r, ?_⟩, ?_⟩
    · have := hubcol_flip (ε₀ := ε₀) (!bar')
      rw [Bool.not_not] at this
      rw [← this]
      simpa [Bool.not_not] using hr
    · simp [flipV, flipHub, Bool.not_not]

/-- A far pair downstairs gives one upstairs, for an onto graph homomorphism. -/
theorem exists_far_of_hom {V V' : Type*} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : V → V')
    (hf : ∀ {x y}, G.Adj x y → G'.Adj (f x) (f y)) (hs : Function.Surjective f)
    (h : ∃ x y, (9 : ℕ∞) ≤ G'.edist x y) : ∃ x y, (9 : ℕ∞) ≤ G.edist x y := by
  obtain ⟨x, y, hxy⟩ := h
  obtain ⟨p, rfl⟩ := hs x
  obtain ⟨q, rfl⟩ := hs y
  refine ⟨p, q, ?_⟩
  unfold SimpleGraph.edist
  refine le_iInf fun W => ?_
  have hW := SimpleGraph.edist_le (W.map ⟨f, hf⟩)
  rw [SimpleGraph.Walk.length_map] at hW
  exact hxy.trans hW

end BipartiteDD.LeanMaxx.Omega45
