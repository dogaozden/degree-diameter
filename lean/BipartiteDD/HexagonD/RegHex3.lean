import BipartiteDD.HexagonD.RegHex2

/-! Theorem D, slice 2, part 25 (target 5): degree lower bounds and twins in the levelled hexagon. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

theorem degL_restrictR_eq {α β : Type*} (r : α → β → Prop) (S : Set β) (a : α) :
    degL (restrictR r S) a = {b : β | r a b ∧ b ∉ S}.ncard := by
  unfold degL restrictR
  rw [← Set.ncard_image_of_injective _ (Subtype.val_injective (p := fun b : β => b ∉ S))]
  congr 1
  ext b
  simp

/-- Every point version keeps at least `q + 1` neighbours after deleting any set of non-pool versions. -/
theorem degL_ge (hc : ¬ IsSquare (-c)) (hm : 0 < m) (S : Set (VR c c0 c1 m))
    (hS : ∀ b ∈ S, isP c c0 c1 hm b) (a : VL c c0 c1 m) :
    Fintype.card F + 1 ≤ degL (restrictR (rr c c0 c1 m) S) a := by
  rw [degL_restrictR_eq, ← ncard_hexInc_lines a.1]
  refine Set.ncard_le_ncard_of_injOn (canR hm a) ?_ ?_ (Set.toFinite _)
  · intro l hl
    refine ⟨rr_canR hm a hl, fun hmem => canR_not_isP hc hm a hl (hS _ hmem)⟩
  · intro l _ l' _ h
    exact congrArg Sigma.fst h

/-- Every line version has at least `q + 1` neighbours. -/
theorem degR_ge (hm : 0 < m) (b : VR c c0 c1 m) :
    Fintype.card F + 1 ≤ degR (rr c c0 c1 m) b := by
  unfold degR
  rw [← ncard_hexInc_points b.1]
  refine Set.ncard_le_ncard_of_injOn (canL hm b) ?_ ?_ (Set.toFinite _)
  · intro p hp
    exact rr_canL hm b hp
  · intro p _ p' _ h
    exact congrArg Sigma.fst h

/-- A deletable version has a surviving twin: the version with last letter `0`. -/
theorem twin_of_isP (hc : ¬ IsSquare (-c)) (hm : 0 < m) {b : VR c c0 c1 m}
    (hb : isP c c0 c1 hm b) : ∃ b' : VR c c0 c1 m, ¬ isP c c0 c1 hm b' ∧
      ∀ a, rr c c0 c1 m a b' ↔ rr c c0 c1 m a b := by
  obtain ⟨hlPi, i, hi, hne⟩ := hb
  refine ⟨⟨b.1, Function.update b.2 i ⟨0, hm⟩⟩, ?_, ?_⟩
  · rintro ⟨-, i', hi', hne'⟩
    have hii : (i' : ℕ) = i := by
      have := hi'.trans hi.symm
      omega
    have e : i' = i := Fin.ext hii
    apply hne'
    exact (congrArg (fun j => Function.update b.2 i ⟨0, hm⟩ j) e).trans (Function.update_self _ _ _)
  · intro a
    constructor
    · rintro ⟨hp, hag⟩
      refine ⟨hp, fun j ha hb' => ?_⟩
      have h1 := hgt_pt_on_sline (c0 := c0) (c1 := c1) hc hlPi hp
      have hji : (⟨j, hb'⟩ : Fin (hgt c c0 c1 (Sum.inr b.1))) ≠ i := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have := hag j ha hb'
      simpa [Function.update_of_ne hji] using this
    · rintro ⟨hp, hag⟩
      refine ⟨hp, fun j ha hb' => ?_⟩
      have h1 := hgt_pt_on_sline (c0 := c0) (c1 := c1) hc hlPi hp
      have hji : (⟨j, hb'⟩ : Fin (hgt c c0 c1 (Sum.inr b.1))) ≠ i := by
        intro h; have := congrArg Fin.val h; simp at this; omega
      have := hag j ha hb'
      simpa [Function.update_of_ne hji] using this

end BipartiteDD.HexagonD
