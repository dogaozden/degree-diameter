import BipartiteDD.HexagonD.RegHex3

/-! Theorem D, slice 2, part 26 (target 5): the sizes of the two sides of the levelled hexagon.

With `q = |F|`, `m ≥ 1`, `W = Wset` the exact whiskers (`|W| + q² = q⁴`):
* `|α| = (q + 1)(1 + q² + q⁴) + (m - 1)((q³ + 1)(q + 1) + m (q + 1))`  (versions of points);
* `|β| = (q + 1)(1 + q² + q⁴) + (m - 1)((q⁴ + q³ + q + 1) + m (q³ + 1) + m²)`  (versions of lines),
so `|β| = |α| + (m - 1) m (q³ + m - q)`. -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon BipartiteDD.Doubling BipartiteDD.Regular
open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)] {c : F} {c0 c1 : F} {m : ℕ}

theorem card_VL (c c0 c1 : F) (m : ℕ) :
    Fintype.card (VL c c0 c1 m) = ∑ p : SPt F, m ^ hgt c c0 c1 (Sum.inl p) := by
  simp [VL, VerL, Fintype.card_sigma, Fintype.card_fun]

theorem card_VR (c c0 c1 : F) (m : ℕ) :
    Fintype.card (VR c c0 c1 m) = ∑ l : HLine F, m ^ hgt c c0 c1 (Sum.inr l) := by
  simp [VR, VerR, Fintype.card_sigma, Fintype.card_fun]

theorem card_filter_pt (c c0 c1 : F) (i : ℕ) :
    (Finset.univ.filter (fun p : SPt F => i < hgt c c0 c1 (Sum.inl p))).card =
      {p : SPt F | Sum.inl p ∈ lev c (vStd : HLine F) (Wset c c0 c1) i}.ncard := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext p
  simp [hgt_iff]

theorem card_filter_line (c c0 c1 : F) (i : ℕ) :
    (Finset.univ.filter (fun l : HLine F => i < hgt c c0 c1 (Sum.inr l))).card =
      {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) i}.ncard := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  congr 1
  ext l
  simp [hgt_iff]

theorem card_VL_eq (hc : ¬ IsSquare (-c)) (hm : 0 < m) :
    Fintype.card (VL c c0 c1 m) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
      (m - 1) * ((Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) + m * (Fintype.card F + 1)) := by
  rw [card_VL, sum_pow_height hm (h := fun p : SPt F => hgt c c0 c1 (Sum.inl p)) (K := 3)
    (fun p => hgt_le c c0 c1 _)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, card_filter_pt]
  have h0 : {p : SPt F | Sum.inl p ∈ lev c (vStd : HLine F) (Wset c c0 c1) 0}.ncard =
      (Fintype.card F ^ 3 + 1) * (Fintype.card F + 1) := by
    rw [← ncard_onPi hc]; congr 1; ext p; simp [lev, A0]
  have h1 : {p : SPt F | Sum.inl p ∈ lev c (vStd : HLine F) (Wset c c0 c1) 1}.ncard =
      Fintype.card F + 1 := by
    rw [← ncard_hexInc_points (vStd : HLine F)]; congr 1; ext p; simp [lev, A1]
  have h2 : {p : SPt F | Sum.inl p ∈ lev c (vStd : HLine F) (Wset c c0 c1) 2}.ncard = 0 := by
    have : {p : SPt F | Sum.inl p ∈ lev c (vStd : HLine F) (Wset c c0 c1) 2} = ∅ := by
      ext p; simp [lev, A2]
    rw [this]; simp
  rw [h0, h1, h2, Fintype.card_eq_nat_card, card_spt_eq]
  ring

theorem card_VR_eq (hc : ¬ IsSquare (-c)) (hG : GoodCubic c c0 c1) (hm : 0 < m) :
    Fintype.card (VR c c0 c1 m) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) +
      (m - 1) * (((Fintype.card F ^ 3 + 1) + Fintype.card F * (Fintype.card F + 1) +
          (Fintype.card F ^ 4 - Fintype.card F ^ 2)) +
        m * (Fintype.card F ^ 3 + 1) + m ^ 2) := by
  rw [card_VR, sum_pow_height hm (h := fun l : HLine F => hgt c c0 c1 (Sum.inr l)) (K := 3)
    (fun l => hgt_le c c0 c1 _)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, card_filter_line]
  have hW := ncard_wset hc hG
  have h0 : {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) 0}.ncard =
      (Fintype.card F ^ 3 + 1) + Fintype.card F * (Fintype.card F + 1) +
        (Fintype.card F ^ 4 - Fintype.card F ^ 2) := by
    have := ncard_L0 hc (vS c) (wset_whiskers hc hG)
    have e : {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) 0} =
        {l : HLine F | InPi c l ∨ Meets (vS c).1 l ∨ l ∈ Wset c c0 c1} := by
      ext l; simp [lev, A0, vS]
    rw [e, this]
    omega
  have h1 : {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) 1}.ncard =
      Fintype.card F ^ 3 + 1 := by
    rw [← ncard_sline hc]; congr 1; ext l; simp [lev, A1]
  have h2 : {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) 2}.ncard = 1 := by
    have : {l : HLine F | Sum.inr l ∈ lev c (vStd : HLine F) (Wset c c0 c1) 2} = {vStd} := by
      ext l; simp [lev, A2]
    rw [this]; simp
  have hH : Nat.card (HLine F) = (Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4) := by
    rw [card_hline, ← card_spt_div, card_spt_eq]
  rw [h0, h1, h2, Fintype.card_eq_nat_card, hH]
  ring

end BipartiteDD.HexagonD
