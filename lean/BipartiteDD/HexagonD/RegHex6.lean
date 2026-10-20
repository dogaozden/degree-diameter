import BipartiteDD.HexagonD.RegHex5

/-! Theorem D, slice 2, part 28 (target 5): **Theorem R** for the hexagon.

For a finite field `F` of odd characteristic (`q = |F|`) and `m ≥ 2`, the levelled doubling of `H(q)` with the exact
whiskers has more lines than points; deleting `S ⊆ P` surplus line versions (each with a surviving twin) leaves a
balanced bipartite graph of diameter `≤ 6` in which every degree is in `[q + 1, q + m]` and the total deficit is large,
so `Regular.regular_of_twins` gives a `(q + m)`-regular bipartite graph of diameter `≤ 6` on `2 |α|` vertices,
`|α| = (q + 1)(q⁴ + q² + 1) + (m - 1)((q³ + 1)(q + 1) + m (q + 1))`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

theorem arith_balance (q t d : ℕ) (hd : q ^ 4 = q ^ 2 + d) :
    (q + 1) * (1 + q ^ 2 + q ^ 4) + t * (((q ^ 3 + 1) + q * (q + 1) + d) + (t + 1) * (q ^ 3 + 1) + (t + 1) ^ 2) +
      t * (t + 1) * q =
    (q + 1) * (1 + q ^ 2 + q ^ 4) + t * ((q ^ 3 + 1) * (q + 1) + (t + 1) * (q + 1)) +
      t * (t + 1) * (q ^ 3 + (t + 1)) := by
  have : (q : ℤ) ^ 4 = q ^ 2 + d := by exact_mod_cast hd
  zify
  linear_combination (-(t : ℤ)) * this

theorem pool_arith (cVR cVL cP a b : ℕ) (hrel : cVR + a = cVL + b) (hP : cP = b) (hab : a ≤ b) :
    cVL ≤ cVR ∧ cVR - cVL ≤ cP ∧ cVR - cVL + a = b := by omega

/-- The deletion set. -/
theorem exists_deletion (hc : ¬ IsSquare (-c)) (hG : GoodCubic c c0 c1) (hm : 0 < m) :
    ∃ S : Finset (VR c c0 c1 m), (∀ b ∈ S, isP c c0 c1 hm b) ∧
      Fintype.card (VL c c0 c1 m) + S.card = Fintype.card (VR c c0 c1 m) ∧
      S.card + (m - 1) * m * Fintype.card F = (m - 1) * m * (Fintype.card F ^ 3 + m) := by
  have hVL := card_VL_eq (c0 := c0) (c1 := c1) hc hm
  have hVR := card_VR_eq hc hG hm
  have hq2 : Fintype.card F ^ 2 ≤ Fintype.card F ^ 4 :=
    Nat.pow_le_pow_right Fintype.card_pos (by norm_num)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hq2
  have hP := card_pool (c0 := c0) (c1 := c1) hc hm
  have hdd : Fintype.card F ^ 4 - Fintype.card F ^ 2 = d := by omega
  rw [hdd] at hVR
  have key := arith_balance (Fintype.card F) (m - 1) d hd
  rw [Nat.sub_add_cancel hm] at key
  have hqle : Fintype.card F ≤ Fintype.card F ^ 3 + m := by
    have : Fintype.card F ≤ Fintype.card F ^ 3 := Nat.le_self_pow (by norm_num) _
    omega
  have hab : (m - 1) * m * Fintype.card F ≤ (m - 1) * m * (Fintype.card F ^ 3 + m) :=
    Nat.mul_le_mul_left _ hqle
  have hrel : Fintype.card (VR c c0 c1 m) + (m - 1) * m * Fintype.card F =
      Fintype.card (VL c c0 c1 m) + (m - 1) * m * (Fintype.card F ^ 3 + m) := by
    rw [hVR, hVL]
    linarith [key]
  have hb : Fintype.card {b : VR c c0 c1 m // isP c c0 c1 hm b} =
      (m - 1) * m * (Fintype.card F ^ 3 + m) := by
    rw [hP]; ring
  obtain ⟨h1, h2, h3⟩ := pool_arith _ _ _ _ _ hrel hb hab
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq
    (s := Finset.univ.filter (fun b : VR c c0 c1 m => isP c c0 c1 hm b))
    (n := Fintype.card (VR c c0 c1 m) - Fintype.card (VL c c0 c1 m)) (by
      rw [← Fintype.card_subtype]; exact h2)
  refine ⟨S, fun b hb => (Finset.mem_filter.1 (hSsub hb)).2, ?_, ?_⟩
  · omega
  · rw [hScard]; exact h3

end BipartiteDD.HexagonD
