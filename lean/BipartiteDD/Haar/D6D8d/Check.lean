import BipartiteDD.Haar.D6D8d.Gens

/-! Covering words for `G`: a code `c` in base `6` gives digits `d₀ … d₇` (indices into `sGl`), and the words
`wAA`, `wAB`, `wBB` are the covering words of `Diam8`. `chkList` runs a check over a list of codes, the
code of index `n` being the `n`-th entry. -/

namespace BipartiteDD.Haar.D6D8d

open BipartiteDD.Haar.D6D8d.PSL11

/-- The generators, as a finset. -/
def sG (i : ℕ) : G := sGl.getD i 1

/-- The generators as a finset of `G`. -/
def SS : Finset G := (Finset.range 6).image sG

theorem sG_mem {i : ℕ} (hi : i < 6) : sG i ∈ SS :=
  Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩

theorem card_SS : SS.card = 6 := by
  decide +kernel

/-- The `k`-th digit of the code `c`. -/
def dig (c k : ℕ) : ℕ := c / 6 ^ k % 6

theorem dig_lt (c k : ℕ) : dig c k < 6 :=
  Nat.mod_lt _ (by norm_num)

def wAA (c : ℕ) : G :=
  (sG (dig c 0))⁻¹ * sG (dig c 1) * ((sG (dig c 2))⁻¹ * sG (dig c 3)) *
    ((sG (dig c 4))⁻¹ * sG (dig c 5)) * ((sG (dig c 6))⁻¹ * sG (dig c 7))

def wAB (c : ℕ) : G :=
  sG (dig c 0) * ((sG (dig c 1))⁻¹ * sG (dig c 2)) * ((sG (dig c 3))⁻¹ * sG (dig c 4)) *
    ((sG (dig c 5))⁻¹ * sG (dig c 6))

def wBB (c : ℕ) : G :=
  sG (dig c 0) * (sG (dig c 1))⁻¹ * (sG (dig c 2) * (sG (dig c 3))⁻¹) *
    (sG (dig c 4) * (sG (dig c 5))⁻¹) * (sG (dig c 6) * (sG (dig c 7))⁻¹)

def chkAA (n c : ℕ) : Bool := decide (gOf n = wAA c)
def chkAB (n c : ℕ) : Bool := decide (gOf n = wAB c)
def chkBB (n c : ℕ) : Bool := decide (gOf n = wBB c)

/-- Checks `f n c` for the codes `c` of `l`, with `c` at index `n`, `n + 1`, …. -/
def chkList (f : ℕ → ℕ → Bool) : ℕ → List ℕ → Bool
  | _, [] => true
  | n, c :: cs => f n c && chkList f (n + 1) cs

theorem chkList_spec (f : ℕ → ℕ → Bool) : ∀ (l : List ℕ) (n : ℕ), chkList f n l = true →
    ∀ j < l.length, f (n + j) (l.getD j 0) = true
  | [], _, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | c :: cs, n, h, j, hj => by
    simp only [chkList, Bool.and_eq_true] at h
    cases j with
    | zero => simpa using h.1
    | succ j =>
      have h2 := chkList_spec f cs (n + 1) h.2 j (by simpa using hj)
      have e : n + (j + 1) = n + 1 + j := by omega
      rw [e]
      simpa using h2

end BipartiteDD.Haar.D6D8d
