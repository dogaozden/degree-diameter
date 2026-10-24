import BipartiteDD.Fast
import BipartiteDD.Haar.LiftD.Formula288

/-! The kernel-checked `checkFast` must reject each broken variant of the 288-vertex lift: a diameter bound of 7,
a degree bound of 2, and a constant colouring. -/

namespace BipartiteDD.LiftD

theorem fast_fails_diameter : BipartiteDD.Fast.checkFast 9 3 7 adjL colL = false := by decide +kernel
theorem fast_fails_degree : BipartiteDD.Fast.checkFast 9 2 8 adjL colL = false := by decide +kernel
theorem fast_fails_colouring : BipartiteDD.Fast.checkFast 9 3 8 adjL (List.replicate 288 false) = false := by
  decide +kernel

end BipartiteDD.LiftD
