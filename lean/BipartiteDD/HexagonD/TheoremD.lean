import BipartiteDD.HexagonD.WCount

/-! Theorem D, slice 2, part 21 (target 4): **Theorem 4 (exact whiskers for every odd `q`)**.

For every finite field `F` of odd characteristic (`q = |F|`) the exact whisker set `Wset` of the report has
`q⁴ - q² = q²(q² - 1)` lines, satisfies the whisker hypotheses, and Delorme's hexagon doubling extended by it gives
`n_b(q + 2, 6) ≥ 2(q + 1)(q⁴ + q² + 1) + 2q⁴ + 4q³ + 4q + 10` (`theoremD_two`; `theoremD` for `q + m`). -/

set_option linter.unusedSectionVars false

namespace BipartiteDD.HexagonD

open BipartiteDD.Hexagon

variable {F : Type*} [Field F] [Fintype F] [NeZero (2 : F)]

/-- **Theorem 4.** There are `c`, `c₀`, `c₁` such that `Wset` is a set of `q²(q² - 1)` whiskers and is exact
(every free point lies on exactly one of its lines). -/
theorem theorem4 : ∃ c c0 c1 : F, ¬ IsSquare (-c) ∧ GoodCubic c c0 c1 ∧
    Whiskers c (vS c) (Wset c c0 c1) ∧
    (Wset c c0 c1).ncard + Fintype.card F ^ 2 = Fintype.card F ^ 4 ∧
    ∀ p : SPt F, p ∈ FreePts c → ∃! m : HLine F, m ∈ Wset c c0 c1 ∧ hexInc p m := by
  obtain ⟨c, hc⟩ := exists_nonsquare_neg (F := F)
  obtain ⟨c0, c1, hG⟩ := exists_goodCubic hc
  exact ⟨c, c0, c1, hc, hG, wset_whiskers hc hG, ncard_wset hc hG,
    fun p hp => exists_unique_wline hc hG hp.1 hp.2⟩

/-- **Theorem D (`q + m`)**: for `m ≥ 1`, a bipartite graph of maximum degree `≤ q + m`, diameter `≤ 6` and
`2(q+1)(q⁴+q²+1) + (m-1)(q⁴+2q³+q²+2q+2 + m(q³+q+2) + m²) + (m-1)(q⁴ - q²)` vertices. -/
theorem theoremD {m : ℕ} (hm : 0 < m) :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (m - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + m * (Fintype.card F ^ 3 + Fintype.card F + 2) + m ^ 2) +
        (m - 1) * (Fintype.card F ^ 4 - Fintype.card F ^ 2))),
      IsBipartiteDegDiam H (Fintype.card F + m) 6 := by
  obtain ⟨c, c0, c1, hc, hG, hW, hcard, -⟩ := theorem4 (F := F)
  have := whiskers_bound_hexagon hc hm (vS c) hW
  have e : (Wset c c0 c1).ncard = Fintype.card F ^ 4 - Fintype.card F ^ 2 := by omega
  rw [e] at this
  exact this

/-- **Theorem D (`q + 2`)**: `n_b(q + 2, 6) ≥ 2(q+1)(q⁴+q²+1) + 2q⁴ + 4q³ + 4q + 10` for odd `q`. -/
theorem theoremD_two :
    ∃ H : SimpleGraph (Fin (2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (2 * Fintype.card F ^ 4 + 4 * Fintype.card F ^ 3 + 4 * Fintype.card F + 10))),
      IsBipartiteDegDiam H (Fintype.card F + 2) 6 := by
  have := theoremD (F := F) (m := 2) (by norm_num)
  have hq : Fintype.card F ^ 2 ≤ Fintype.card F ^ 4 :=
    Nat.pow_le_pow_right Fintype.card_pos (by norm_num)
  have e : 2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (2 - 1) * ((Fintype.card F ^ 4 + 2 * Fintype.card F ^ 3 + Fintype.card F ^ 2 +
          2 * Fintype.card F + 2) + 2 * (Fintype.card F ^ 3 + Fintype.card F + 2) + 2 ^ 2) +
        (2 - 1) * (Fintype.card F ^ 4 - Fintype.card F ^ 2) =
      2 * ((Fintype.card F + 1) * (1 + Fintype.card F ^ 2 + Fintype.card F ^ 4)) +
        (2 * Fintype.card F ^ 4 + 4 * Fintype.card F ^ 3 + 4 * Fintype.card F + 10) := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hq
    rw [hd, Nat.add_sub_cancel_left]
    have : Fintype.card F ^ 4 = Fintype.card F ^ 2 + d := hd
    norm_num
    nlinarith [this]
  rw [e] at this
  exact this

end BipartiteDD.HexagonD
