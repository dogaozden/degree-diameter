import BipartiteDD.LeanMaxx.Omega45.Cover

/-!
# The case `q = 7`: radius-2 families, by kernel evaluation

For `q = 7` (`α ≤ 5`, since `2 α ≤ q + 3 = 10`) and every block pattern `typ : Fin α → Bool` (`decide +kernel`;
no extra axiom), for the missed copy `cstar` of Lemma 3.2:

* `|D2| ≤ 140`, the number of radius-2 centre words that matter (`Cover.lean`; the worst values over all patterns
  are `4, 23, 52, 91, 140` for `α = 1, …, 5`; this is the bound `m₂ ≤ 140` of §4 of the note),
* `|F0| = α`: exactly one radius-4 centre per block, so the pair `(0, cstar)` is *starved* in the sense of §4 of
  the note when `α = 5`.
-/

set_option maxRecDepth 100000

namespace BipartiteDD.LeanMaxx.Omega45

open BipartiteDD.LeanMaxx.Omega3 BipartiteDD.LeanMaxx.Omega45

theorem tab7_1 : ∀ typ : Fin 1 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 1 := by decide +kernel
theorem tab7_2 : ∀ typ : Fin 2 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 2 := by decide +kernel
theorem tab7_3 : ∀ typ : Fin 3 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 3 := by decide +kernel
theorem tab7_4 : ∀ typ : Fin 4 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 4 := by decide +kernel
theorem tab7_5 : ∀ typ : Fin 5 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 5 := by decide +kernel

variable {α : ℕ} (typ : Fin α → Bool)

theorem star7 (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3) :
    (D2 typ (cstar typ hα)).card ≤ 140 ∧ (F0 typ 0 (cstar typ hα)).card = α := by
  have : α ≤ 5 := by omega
  interval_cases α
  exacts [tab7_1 typ, tab7_2 typ, tab7_3 typ, tab7_4 typ, tab7_5 typ]

end BipartiteDD.LeanMaxx.Omega45
