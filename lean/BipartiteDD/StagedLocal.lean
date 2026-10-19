import BipartiteDD.Staged

/-! The local test of `Staged`, split by vertex ranges.

On the largest graphs the local test on all vertices is too much for one kernel check, so it is run
on two halves, `checkLocalRange 0 m` and `checkLocalRange m (n - m)`. `checkLocal_of_split` shows
that the two halves together give `checkLocal`. -/

namespace BipartiteDD.Staged

open BipartiteDD.Fast

/-- The local test of `checkLocal`, on the vertices `lo, lo + 1, ..., lo + cnt - 1`. -/
def checkLocalRange (K d : ℕ) {n : ℕ} (adj : List (List (Fin n))) (col : List Bool) (lo cnt : ℕ) :
    Bool :=
  let adjT := Tree.build [] K adj
  let colT := Tree.build false K col
  (List.range' lo cnt).all fun u =>
    decide ((Tree.get [] K adjT u).length ≤ d) &&
    (Tree.get [] K adjT u).all (fun v =>
      (Tree.get [] K adjT v.val).any (fun w => w.val == u) &&
      (Tree.get false K colT u != Tree.get false K colT v.val))

/-- Two vertex ranges that cover `0 .. n - 1` give the local test `checkLocal`. -/
theorem checkLocal_of_split {K d n : ℕ} {adj : List (List (Fin n))} {col : List Bool} (m : ℕ)
    (hm : m ≤ n) (h1 : checkLocalRange K d adj col 0 m = true)
    (h2 : checkLocalRange K d adj col m (n - m) = true) :
    checkLocal K d adj col = true := by
  unfold checkLocal
  rw [List.all_eq_true]
  intro u hu
  rw [List.mem_range] at hu
  unfold checkLocalRange at h1 h2
  by_cases hum : u < m
  · exact List.all_eq_true.mp h1 u (List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega⟩)
  · exact List.all_eq_true.mp h2 u (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

end BipartiteDD.Staged
