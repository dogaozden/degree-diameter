import BipartiteDD.ASq.Main
import BipartiteDD.Regular.Defs

/-! Regularity, part 3: Theorem A is regular.

The `AS(q)` quadrangle of order `(q - 1, q + 1)` with the weighted 2-ovoid `wt` has copy graph with every
point of degree `q + 2` already (a point lies on `q + 2` lines and has no line copies) and every line with
exactly two point copies, hence degree `q + 2` too. `GQST.regular_copy_graph_fin` with `Δ = q + 2` and no line
copies says the graph is `(q + 2)`-regular, bipartite and of diameter at most `4`, with the same vertex count
`2 q² (q + 2)`. -/

namespace BipartiteDD.ASq

open scoped Classical

/-- **Theorem A is regular.** For every finite field of odd order `q` there is a `(q + 2)`-regular bipartite
graph on `2 q² (q + 2)` vertices of diameter at most `4`. -/
theorem bound_regular {F : Type*} [Field F] [Fintype F] {q : ℕ} (hq : Fintype.card F = q)
    (hF : ringChar F ≠ 2) :
    ∃ H : SimpleGraph (Fin (2 * q ^ 2 * (q + 2))), IsBipartiteRegDiam H (q + 2) 4 := by
  obtain ⟨ε, hε⟩ := FiniteField.exists_nonsquare hF
  have h2 := two_ne_zero_of_ringChar hF
  have hε0 : ε ≠ 0 := fun h => hε ⟨0, by simp [h]⟩
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have h4ε : 4 * ε ≠ 0 := mul_ne_zero h4 hε0
  have hc : (1 : F) * (1 / (4 * ε)) = 1 / (4 * ε) := one_mul _
  let _inst : Fintype (Line F) := Fintype.ofFinite _
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  have hs : Fintype.card F - 1 + 1 = q := by omega
  -- every line carries total weight `2 = Δ - (s + 1)`, every point total line weight `0 = Δ - (t + 1)`
  have hw : ∀ l : Line F, ∑ p ∈ Finset.univ.filter (fun p : F × F × F => p ∈ l),
      wt ε 1 (1 / (4 * ε)) p = q + 2 - (Fintype.card F - 1 + 1) := fun l => by
    rw [weighted_two_ovoid hF hε hc l, hs]
    omega
  have hm : ∀ p : F × F × F, ∑ l ∈ Finset.univ.filter (fun l : Line F => p ∈ l),
      (fun _ : Line F => (0 : ℕ)) l = q + 2 - (Fintype.card F + 1 + 1) := fun p => by
    simp only [Finset.sum_const_zero]
    omega
  obtain ⟨H, hc2, hd, he⟩ := GQST.regular_copy_graph_fin (isGQst hF) (q + 2) (by omega) (by omega) hw hm
  -- counting lines: `|P| (t + 1) = |L| (s + 1)`
  have hL := card_mul_eq (isGQst hF)
  have hP : Fintype.card (F × F × F) = q ^ 3 := by
    simp only [Fintype.card_prod, hq]
    ring
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
  exact ⟨H.comap (finCongr hn).symm, IsBipartiteRegDiam.comap ⟨hc2, hd, he⟩ (finCongr hn)⟩

end BipartiteDD.ASq
