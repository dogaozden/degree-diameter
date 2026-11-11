import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! The arithmetic of Theorem 4.1 (`research/theorems/HAAR_D8_10.md`, §4.1).

Write `k = Δ - 1`. The layer bound is `bnd k 0 = 1` and `bnd k L = (k + 1) k^(L-1)` for `L ≥ 1`
(that is `Δ (Δ - 1)^(L-1)`). Summing it over the lengths `L < D` with the parity of `D - 1` telescopes to
`∑_{j < D} k^j`, because `(k+1) k^(L-1) = k^L + k^(L-1)` pairs the layers. -/

namespace BipartiteDD.LeanMaxx.HaarBound

open Finset

/-- The layer bound: `1` for the identity layer and `Δ (Δ - 1)^(L-1)` for `L ≥ 1`, with `Δ = k + 1`. -/
def bnd (k L : ℕ) : ℕ := if L = 0 then 1 else (k + 1) * k ^ (L - 1)

/-- The sum of the layer bounds over `L < D` with `L ≡ D - 1 (mod 2)`. -/
def parSum (k D : ℕ) : ℕ :=
  ∑ L ∈ (range D).filter (fun L => L % 2 = (D + 1) % 2), bnd k L

theorem bnd_succ (k D : ℕ) : bnd k (D + 1) = k ^ (D + 1) + k ^ D := by
  unfold bnd
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
  ring

theorem filter_range_add_two (D : ℕ) :
    (range (D + 2)).filter (fun L => L % 2 = (D + 2 + 1) % 2)
      = insert (D + 1) ((range D).filter (fun L => L % 2 = (D + 1) % 2)) := by
  ext L
  simp only [mem_filter, mem_range, mem_insert]
  omega

theorem parSum_add_two (k D : ℕ) : parSum k (D + 2) = parSum k D + (k ^ D + k ^ (D + 1)) := by
  unfold parSum
  rw [filter_range_add_two, sum_insert, bnd_succ]
  · ring
  · simp

theorem parSum_eq (k : ℕ) : ∀ D, parSum k D = ∑ j ∈ range D, k ^ j
  | 0 => by simp [parSum]
  | 1 => by
    rw [parSum, Finset.sum_filter, Finset.sum_range_one]
    simp [bnd]
  | D + 2 => by
    rw [parSum_add_two, parSum_eq k D, sum_range_succ, sum_range_succ]
    ring

end BipartiteDD.LeanMaxx.HaarBound
