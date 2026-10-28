import BipartiteDD.LeanMaxx.Omega3.Wiring

/-!
# The cases `q = 8, 9` of Theorem 3.3: exact counts, by kernel evaluation

For `q = 8` (`α ≤ 5`) and `q = 9` (`α ≤ 6`) the crude bound on the number of radius-2 balls is not enough.
Here the inequality `|F0| (q⁴ + 2q²) + m2 q² < q⁵` is checked for every block pattern `typ : Fin α → Bool`
(`decide +kernel`: kernel evaluation of a decidable proposition; it adds no axiom).
The worst values of `m2` are 5, 25, 55, 95, 145, 207 for `α = 1, …, 6`.
-/

set_option maxRecDepth 100000

namespace BipartiteDD.LeanMaxx.Omega3

theorem tab8_1 : ∀ typ : Fin 1 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (8 ^ 4 + 2 * 8 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 8 ^ 2 < 8 ^ 5 := by
  decide +kernel

theorem tab8_2 : ∀ typ : Fin 2 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (8 ^ 4 + 2 * 8 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 8 ^ 2 < 8 ^ 5 := by
  decide +kernel

theorem tab8_3 : ∀ typ : Fin 3 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (8 ^ 4 + 2 * 8 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 8 ^ 2 < 8 ^ 5 := by
  decide +kernel

theorem tab8_4 : ∀ typ : Fin 4 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (8 ^ 4 + 2 * 8 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 8 ^ 2 < 8 ^ 5 := by
  decide +kernel

theorem tab8_5 : ∀ typ : Fin 5 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (8 ^ 4 + 2 * 8 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 8 ^ 2 < 8 ^ 5 := by
  decide +kernel

theorem tab9_1 : ∀ typ : Fin 1 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel

theorem tab9_2 : ∀ typ : Fin 2 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel

theorem tab9_3 : ∀ typ : Fin 3 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel

theorem tab9_4 : ∀ typ : Fin 4 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel

theorem tab9_5 : ∀ typ : Fin 5 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel

theorem tab9_6 : ∀ typ : Fin 6 → Bool,
    (F0 typ 0 (cstar typ (by omega))).card * (9 ^ 4 + 2 * 9 ^ 2) + m2 typ 0 (cstar typ (by omega)) * 9 ^ 2 < 9 ^ 5 := by
  decide +kernel


variable {α : ℕ} (typ : Fin α → Bool)

theorem star_small {q : ℕ} (hα : 0 < α) (hq : q = 8 ∨ q = 9) (h2 : 2 * α ≤ q + 3) :
    (F0 typ 0 (cstar typ hα)).card * (q ^ 4 + 2 * q ^ 2) + m2 typ 0 (cstar typ hα) * q ^ 2 < q ^ 5 := by
  rcases hq with rfl | rfl
  · have : α ≤ 5 := by omega
    interval_cases α
    exacts [tab8_1 typ, tab8_2 typ, tab8_3 typ, tab8_4 typ, tab8_5 typ]
  · have : α ≤ 6 := by omega
    interval_cases α
    exacts [tab9_1 typ, tab9_2 typ, tab9_3 typ, tab9_4 typ, tab9_5 typ, tab9_6 typ]

/-- **The counting hypothesis of Theorem 3.3** for every `q ≥ 8`: the missed copy `cstar` is not met by the
unbarred class `0`, and the radius-4 and radius-2 balls cannot cover the vertices opposite a hub. -/
theorem star_exists {q : ℕ} (hα : 0 < α) (hq : 8 ≤ q) (h2 : 2 * α ≤ q + 3) :
    cstar typ hα ∉ CuK typ 0 ∧
      (F0 typ 0 (cstar typ hα)).card * (q ^ 4 + 2 * q ^ 2) + m2 typ 0 (cstar typ hα) * q ^ 2 < q ^ 5 := by
  refine ⟨cstar_not_mem typ hα, ?_⟩
  by_cases h : q = 8 ∨ q = 9
  · exact star_small typ hα h h2
  · exact star_crude typ hα (by omega) h2

end BipartiteDD.LeanMaxx.Omega3
