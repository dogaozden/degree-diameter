import Mathlib

/-!
# The counting bound `A + B + 1 < q⁵`

`sB q d` is the sphere size `s_d` (`s₀ = 1`, `s_d = (q+1) q^(d-1)`).
`pairs1` are the pairs `(d₁, d₂)` with `d₁ + d₂ ≤ 4` even, `triples2` the triples with sum `≤ 2`.
`sumA q = Σ_{pairs1} s_{d₁} s_{d₂}` and `sumB q = Σ_{triples2} s_{d₁} s_{d₂} s_{d₃}` are the numbers
`A` and `B` of the note; `count_lt` says `A + B + 1 < q⁵` for `q ≥ 7`.
-/

namespace BipartiteDD.LeanMaxx.Omega2

open Finset

/-- The sphere size `s_d`. -/
def sB (q d : ℕ) : ℕ := if d = 0 then 1 else (q + 1) * q ^ (d - 1)

def pairs1 : Finset (ℕ × ℕ) := (range 5 ×ˢ range 5).filter fun p => p.1 + p.2 ≤ 4 ∧ Even (p.1 + p.2)

def triples2 : Finset (ℕ × ℕ × ℕ) :=
  (range 3 ×ˢ range 3 ×ˢ range 3).filter fun t => t.1 + t.2.1 + t.2.2 ≤ 2

def sumA (q : ℕ) : ℕ := ∑ p ∈ pairs1, sB q p.1 * sB q p.2

def sumB (q : ℕ) : ℕ := ∑ t ∈ triples2, sB q t.1 * sB q t.2.1 * sB q t.2.2

theorem pairs1_eq : pairs1 = {(0,0),(0,2),(2,0),(1,1),(0,4),(4,0),(1,3),(3,1),(2,2)} := by decide

theorem triples2_eq : triples2 = {(0,0,0),(1,0,0),(0,1,0),(0,0,1),(2,0,0),(0,2,0),(0,0,2),
    (1,1,0),(1,0,1),(0,1,1)} := by decide

theorem sumA_eq (q : ℕ) : sumA q = 1 + 2 * ((q + 1) * q) + (q + 1) ^ 2 + 2 * ((q + 1) * q ^ 3)
    + 3 * ((q + 1) ^ 2 * q ^ 2) := by
  unfold sumA
  rw [pairs1_eq]
  simp [sB, Finset.sum_insert]
  ring

theorem sumB_eq (q : ℕ) : sumB q = 1 + 3 * (q + 1) + 3 * ((q + 1) * q) + 3 * (q + 1) ^ 2 := by
  unfold sumB
  rw [triples2_eq]
  simp [sB, Finset.sum_insert]
  ring

theorem count_lt {q : ℕ} (hq : 7 ≤ q) : sumA q + sumB q + 1 < q ^ 5 := by
  rw [sumA_eq, sumB_eq]
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
  ring_nf
  omega

end BipartiteDD.LeanMaxx.Omega2
