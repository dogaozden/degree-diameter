import BipartiteDD.HexagonD.RegHex4

/-! Theorem D, slice 2, part 27 (target 5): the pool of deletable versions and the set `S` to delete.

The pool `P = {b | isP b}` (versions of spread lines with last letter nonzero) has
`(m - 1) (m q³ + m²)` elements, at least the excess `|β| - |α| = (m - 1) m (q³ + m - q)`; so there is a finset
`S ⊆ P` with `|α| + |S| = |β|` (`exists_deletion`). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

/-- Strings of length `n + 1` with nonzero last letter. -/
theorem card_lastne {m : ℕ} (hm : 0 < m) (n : ℕ) :
    Fintype.card {t : Fin (n + 1) → Fin m // t (Fin.last n) ≠ ⟨0, hm⟩} = (m - 1) * m ^ n := by
  let e := (Fin.snocEquiv (fun _ : Fin (n + 1) => Fin m)).symm
  have e1 : {t : Fin (n + 1) → Fin m // t (Fin.last n) ≠ ⟨0, hm⟩} ≃
      {x : Fin m × (Fin n → Fin m) // x.1 ≠ ⟨0, hm⟩} :=
    e.subtypeEquiv (fun t => by simp [e, Fin.snocEquiv])
  have e2 : {x : Fin m × (Fin n → Fin m) // x.1 ≠ ⟨0, hm⟩} ≃
      {j : Fin m // j ≠ ⟨0, hm⟩} × {t : Fin n → Fin m // True} :=
    (Equiv.subtypeEquivRight (fun x => by simp)).trans
      (Equiv.subtypeProdEquivProd (p := fun j : Fin m => j ≠ ⟨0, hm⟩) (q := fun _ : Fin n → Fin m => True))
  rw [Fintype.card_congr (e1.trans e2), Fintype.card_prod]
  have h1 : Fintype.card {j : Fin m // j ≠ ⟨0, hm⟩} = m - 1 := by
    have := Fintype.card_subtype_compl (fun j : Fin m => j = ⟨0, hm⟩)
    rw [Fintype.card_subtype_eq] at this
    simpa using this
  have h2 : Fintype.card {t : Fin n → Fin m // True} = m ^ n := by
    simp [Fintype.card_subtype_true, Fintype.card_fun]
  rw [h1, h2]

/-- The same with an abstract length `N > 0`. -/
theorem card_lastne' {m : ℕ} (hm : 0 < m) {N : ℕ} (hN : 0 < N) :
    Fintype.card {t : Fin N → Fin m // ∃ i : Fin N, i.1 + 1 = N ∧ t i ≠ ⟨0, hm⟩} = (m - 1) * m ^ (N - 1) := by
  cases N with
  | zero => omega
  | succ n =>
    rw [Nat.add_sub_cancel, ← card_lastne hm n]
    refine Fintype.card_congr (Equiv.subtypeEquivRight (fun t => ⟨?_, fun h => ⟨Fin.last n, by simp, h⟩⟩))
    rintro ⟨i, hi, h⟩
    have : i = Fin.last n := Fin.ext (by simp; omega)
    subst this
    exact h

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

theorem card_pool (hc : ¬ IsSquare (-c)) (hm : 0 < m) :
    Fintype.card {b : VR c c0 c1 m // isP c c0 c1 hm b} =
      (m - 1) * m ^ 2 + Fintype.card F ^ 3 * ((m - 1) * m) := by
  let e : {b : VR c c0 c1 m // isP c c0 c1 hm b} ≃
      Σ ℓ : SLine c, {t : Fin (hgt c c0 c1 (Sum.inr ℓ.1)) → Fin m //
        ∃ i : Fin (hgt c c0 c1 (Sum.inr ℓ.1)), i.1 + 1 = hgt c c0 c1 (Sum.inr ℓ.1) ∧ t i ≠ ⟨0, hm⟩} :=
    { toFun := fun b => ⟨⟨b.1.1, b.2.1⟩, ⟨b.1.2, b.2.2⟩⟩
      invFun := fun x => ⟨⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩⟩
      left_inv := fun b => rfl
      right_inv := fun x => rfl }
  have hpos : ∀ ℓ : SLine c, 0 < hgt c c0 c1 (Sum.inr ℓ.1) := fun ℓ => by
    by_cases h : ℓ.1 = vStd
    · rw [h, hgt_v]; omega
    · rw [hgt_sline ℓ.2 h]; omega
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [card_lastne' hm (hpos _)]
  have hv : (vS c) = (⟨vStd, vStd_inPi c⟩ : SLine c) := rfl
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ (vS c))]
  have h1 : (m - 1) * m ^ (hgt c c0 c1 (Sum.inr (vS c).1) - 1) = (m - 1) * m ^ 2 := by
    show (m - 1) * m ^ (hgt c c0 c1 (Sum.inr (vStd : HLine F)) - 1) = _
    rw [hgt_v]
  have h2 : ∑ ℓ ∈ Finset.univ.erase (vS c), (m - 1) * m ^ (hgt c c0 c1 (Sum.inr ℓ.1) - 1) =
      ∑ ℓ ∈ Finset.univ.erase (vS c), (m - 1) * m := by
    refine Finset.sum_congr rfl (fun ℓ hℓ => ?_)
    have : ℓ.1 ≠ vStd := fun h => Finset.ne_of_mem_erase hℓ (Subtype.ext h)
    rw [hgt_sline ℓ.2 this]
    simp
  rw [h1, h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    card_sline hc]
  simp [mul_comm]

end BipartiteDD.HexagonD
