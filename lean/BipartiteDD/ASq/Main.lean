import BipartiteDD.ASq.Weight
import BipartiteDD.GQST.Main

/-! ASq, part 4: the bound.

Take the quadrangle `ASq.isGQst` of order `(q - 1, q + 1)` with the weight `wt` of Theorem A (total
weight `2` on every line) and no line copies. The group-GQST theorem `GQST.gqst` with `a = 2` and `b = 0`
gives a bipartite graph of maximum degree `q + 2` and diameter `4`. Its vertex count is
`q³ + q²(q + 2) + 2q² = 2 q² (q + 2)`. -/

namespace BipartiteDD.ASq

open scoped Classical

/-- Statement 3: for every finite field of odd order `q`, there is a bipartite graph on
`2 q² (q + 2)` vertices with maximum degree `q + 2` and diameter `4`. -/
theorem bound {F : Type*} [Field F] [Fintype F] {q : ℕ} (hq : Fintype.card F = q)
    (hF : ringChar F ≠ 2) :
    ∃ H : SimpleGraph (Fin (2 * q ^ 2 * (q + 2))), IsBipartiteDegDiam H (q + 2) 4 := by
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare hF
  have h2 := two_ne_zero_of_ringChar hF
  have hε0 : ε ≠ 0 := fun h => hε ⟨0, by simp [h]⟩
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4ε : 4 * ε ≠ 0 := mul_ne_zero h4 hε0
  -- `c1 = 1` and `c2 = 1 / (4 ε)`
  have hc : (1 : F) * (1 / (4 * ε)) = 1 / (4 * ε) := one_mul _
  letI : Fintype (Line F) := Fintype.ofFinite _
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hw : ∀ l : Line F, ∑ p ∈ Finset.univ.filter (fun p => p ∈ l), wt ε 1 (1 / (4 * ε)) p ≤ 2 :=
    fun l => (weighted_two_ovoid hF hε hc l).le
  have hm : ∀ p : F × F × F, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), (fun _ : Line F => 0) l ≤ 0 :=
    fun p => by simp
  obtain ⟨H, hH⟩ := GQST.gqst (isGQst hF) (wt ε 1 (1 / (4 * ε))) (fun _ => 0) 2 0 hw hm
  -- counting lines: `|P| (t + 1) = |L| (s + 1)`
  have hL := card_mul_eq (isGQst hF)
  have hP : Fintype.card (F × F × F) = q ^ 3 := by
    simp only [Fintype.card_prod, hq]
    ring
  have hs : Fintype.card F - 1 + 1 = q := by omega
  rw [hP, hs, hq] at hL
  have hLq : Fintype.card (Line F) = q ^ 2 * (q + 2) := by
    have hq0 : 0 < q := hq ▸ hpos
    have h' : Fintype.card (Line F) * q = q ^ 2 * (q + 2) * q := by
      rw [← hL]
      ring
    exact Nat.eq_of_mul_eq_mul_right hq0 h'
  have hn : Fintype.card (F × F × F) + Fintype.card (Line F) + ∑ p, wt ε 1 (1 / (4 * ε)) p +
      ∑ _l : Line F, (0 : ℕ) = 2 * q ^ 2 * (q + 2) := by
    rw [hP, hLq, sum_wt, hq]
    simp only [Finset.sum_const_zero, add_zero]
    ring
  have hdeg : max (Fintype.card F - 1 + 1 + 2) (Fintype.card F + 1 + 1 + 0) = q + 2 := by
    rw [max_eq_right (by omega)]
    omega
  rw [hdeg] at hH
  exact ⟨H.comap (finCongr hn).symm, isBipartiteDegDiam_comap (finCongr hn) hH⟩

end BipartiteDD.ASq
