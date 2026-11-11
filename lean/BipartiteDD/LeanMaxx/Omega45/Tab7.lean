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
theorem tab7_5_00000 : (D2 (![false,false,false,false,false] : Fin 5 → Bool) (cstar (![false,false,false,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,false,false,false] : Fin 5 → Bool) 0 (cstar (![false,false,false,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00001 : (D2 (![false,false,false,false,true] : Fin 5 → Bool) (cstar (![false,false,false,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,false,false,true] : Fin 5 → Bool) 0 (cstar (![false,false,false,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00010 : (D2 (![false,false,false,true,false] : Fin 5 → Bool) (cstar (![false,false,false,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,false,true,false] : Fin 5 → Bool) 0 (cstar (![false,false,false,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00011 : (D2 (![false,false,false,true,true] : Fin 5 → Bool) (cstar (![false,false,false,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,false,true,true] : Fin 5 → Bool) 0 (cstar (![false,false,false,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00100 : (D2 (![false,false,true,false,false] : Fin 5 → Bool) (cstar (![false,false,true,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,true,false,false] : Fin 5 → Bool) 0 (cstar (![false,false,true,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00101 : (D2 (![false,false,true,false,true] : Fin 5 → Bool) (cstar (![false,false,true,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,true,false,true] : Fin 5 → Bool) 0 (cstar (![false,false,true,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00110 : (D2 (![false,false,true,true,false] : Fin 5 → Bool) (cstar (![false,false,true,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,true,true,false] : Fin 5 → Bool) 0 (cstar (![false,false,true,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_00111 : (D2 (![false,false,true,true,true] : Fin 5 → Bool) (cstar (![false,false,true,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,false,true,true,true] : Fin 5 → Bool) 0 (cstar (![false,false,true,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01000 : (D2 (![false,true,false,false,false] : Fin 5 → Bool) (cstar (![false,true,false,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,false,false,false] : Fin 5 → Bool) 0 (cstar (![false,true,false,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01001 : (D2 (![false,true,false,false,true] : Fin 5 → Bool) (cstar (![false,true,false,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,false,false,true] : Fin 5 → Bool) 0 (cstar (![false,true,false,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01010 : (D2 (![false,true,false,true,false] : Fin 5 → Bool) (cstar (![false,true,false,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,false,true,false] : Fin 5 → Bool) 0 (cstar (![false,true,false,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01011 : (D2 (![false,true,false,true,true] : Fin 5 → Bool) (cstar (![false,true,false,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,false,true,true] : Fin 5 → Bool) 0 (cstar (![false,true,false,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01100 : (D2 (![false,true,true,false,false] : Fin 5 → Bool) (cstar (![false,true,true,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,true,false,false] : Fin 5 → Bool) 0 (cstar (![false,true,true,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01101 : (D2 (![false,true,true,false,true] : Fin 5 → Bool) (cstar (![false,true,true,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,true,false,true] : Fin 5 → Bool) 0 (cstar (![false,true,true,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01110 : (D2 (![false,true,true,true,false] : Fin 5 → Bool) (cstar (![false,true,true,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,true,true,false] : Fin 5 → Bool) 0 (cstar (![false,true,true,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_01111 : (D2 (![false,true,true,true,true] : Fin 5 → Bool) (cstar (![false,true,true,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![false,true,true,true,true] : Fin 5 → Bool) 0 (cstar (![false,true,true,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10000 : (D2 (![true,false,false,false,false] : Fin 5 → Bool) (cstar (![true,false,false,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,false,false,false] : Fin 5 → Bool) 0 (cstar (![true,false,false,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10001 : (D2 (![true,false,false,false,true] : Fin 5 → Bool) (cstar (![true,false,false,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,false,false,true] : Fin 5 → Bool) 0 (cstar (![true,false,false,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10010 : (D2 (![true,false,false,true,false] : Fin 5 → Bool) (cstar (![true,false,false,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,false,true,false] : Fin 5 → Bool) 0 (cstar (![true,false,false,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10011 : (D2 (![true,false,false,true,true] : Fin 5 → Bool) (cstar (![true,false,false,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,false,true,true] : Fin 5 → Bool) 0 (cstar (![true,false,false,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10100 : (D2 (![true,false,true,false,false] : Fin 5 → Bool) (cstar (![true,false,true,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,true,false,false] : Fin 5 → Bool) 0 (cstar (![true,false,true,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10101 : (D2 (![true,false,true,false,true] : Fin 5 → Bool) (cstar (![true,false,true,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,true,false,true] : Fin 5 → Bool) 0 (cstar (![true,false,true,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10110 : (D2 (![true,false,true,true,false] : Fin 5 → Bool) (cstar (![true,false,true,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,true,true,false] : Fin 5 → Bool) 0 (cstar (![true,false,true,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_10111 : (D2 (![true,false,true,true,true] : Fin 5 → Bool) (cstar (![true,false,true,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,false,true,true,true] : Fin 5 → Bool) 0 (cstar (![true,false,true,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11000 : (D2 (![true,true,false,false,false] : Fin 5 → Bool) (cstar (![true,true,false,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,false,false,false] : Fin 5 → Bool) 0 (cstar (![true,true,false,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11001 : (D2 (![true,true,false,false,true] : Fin 5 → Bool) (cstar (![true,true,false,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,false,false,true] : Fin 5 → Bool) 0 (cstar (![true,true,false,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11010 : (D2 (![true,true,false,true,false] : Fin 5 → Bool) (cstar (![true,true,false,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,false,true,false] : Fin 5 → Bool) 0 (cstar (![true,true,false,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11011 : (D2 (![true,true,false,true,true] : Fin 5 → Bool) (cstar (![true,true,false,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,false,true,true] : Fin 5 → Bool) 0 (cstar (![true,true,false,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11100 : (D2 (![true,true,true,false,false] : Fin 5 → Bool) (cstar (![true,true,true,false,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,true,false,false] : Fin 5 → Bool) 0 (cstar (![true,true,true,false,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11101 : (D2 (![true,true,true,false,true] : Fin 5 → Bool) (cstar (![true,true,true,false,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,true,false,true] : Fin 5 → Bool) 0 (cstar (![true,true,true,false,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11110 : (D2 (![true,true,true,true,false] : Fin 5 → Bool) (cstar (![true,true,true,true,false] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,true,true,false] : Fin 5 → Bool) 0 (cstar (![true,true,true,true,false] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

theorem tab7_5_11111 : (D2 (![true,true,true,true,true] : Fin 5 → Bool) (cstar (![true,true,true,true,true] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![true,true,true,true,true] : Fin 5 → Bool) 0 (cstar (![true,true,true,true,true] : Fin 5 → Bool) (by omega))).card = 5 := by decide +kernel

/-- All 32 patterns, case by case (each leaf is a separate kernel evaluation). -/
theorem tab7_5_all : ∀ a b c d e : Bool,
    (D2 (![a, b, c, d, e] : Fin 5 → Bool) (cstar (![a, b, c, d, e] : Fin 5 → Bool) (by omega))).card ≤ 140 ∧
    (F0 (![a, b, c, d, e] : Fin 5 → Bool) 0 (cstar (![a, b, c, d, e] : Fin 5 → Bool) (by omega))).card = 5 := by
  intro a b c d e
  cases a
  ·
    cases b
    ·
      cases c
      ·
        cases d
        ·
          cases e
          · exact tab7_5_00000
          · exact tab7_5_00001
        ·
          cases e
          · exact tab7_5_00010
          · exact tab7_5_00011
      ·
        cases d
        ·
          cases e
          · exact tab7_5_00100
          · exact tab7_5_00101
        ·
          cases e
          · exact tab7_5_00110
          · exact tab7_5_00111
    ·
      cases c
      ·
        cases d
        ·
          cases e
          · exact tab7_5_01000
          · exact tab7_5_01001
        ·
          cases e
          · exact tab7_5_01010
          · exact tab7_5_01011
      ·
        cases d
        ·
          cases e
          · exact tab7_5_01100
          · exact tab7_5_01101
        ·
          cases e
          · exact tab7_5_01110
          · exact tab7_5_01111
  ·
    cases b
    ·
      cases c
      ·
        cases d
        ·
          cases e
          · exact tab7_5_10000
          · exact tab7_5_10001
        ·
          cases e
          · exact tab7_5_10010
          · exact tab7_5_10011
      ·
        cases d
        ·
          cases e
          · exact tab7_5_10100
          · exact tab7_5_10101
        ·
          cases e
          · exact tab7_5_10110
          · exact tab7_5_10111
    ·
      cases c
      ·
        cases d
        ·
          cases e
          · exact tab7_5_11000
          · exact tab7_5_11001
        ·
          cases e
          · exact tab7_5_11010
          · exact tab7_5_11011
      ·
        cases d
        ·
          cases e
          · exact tab7_5_11100
          · exact tab7_5_11101
        ·
          cases e
          · exact tab7_5_11110
          · exact tab7_5_11111

theorem tab7_5 : ∀ typ : Fin 5 → Bool, (D2 typ (cstar typ (by omega))).card ≤ 140 ∧
    (F0 typ 0 (cstar typ (by omega))).card = 5 := by
  intro typ
  have h : (![typ 0, typ 1, typ 2, typ 3, typ 4] : Fin 5 → Bool) = typ := by
    funext i; fin_cases i <;> rfl
  have := tab7_5_all (typ 0) (typ 1) (typ 2) (typ 3) (typ 4)
  rw [h] at this
  exact this

variable {α : ℕ} (typ : Fin α → Bool)

theorem star7 (hα : 0 < α) (h2 : 2 * α ≤ 7 + 3) :
    (D2 typ (cstar typ hα)).card ≤ 140 ∧ (F0 typ 0 (cstar typ hα)).card = α := by
  have : α ≤ 5 := by omega
  interval_cases α
  exacts [tab7_1 typ, tab7_2 typ, tab7_3 typ, tab7_4 typ, tab7_5 typ]

end BipartiteDD.LeanMaxx.Omega45
