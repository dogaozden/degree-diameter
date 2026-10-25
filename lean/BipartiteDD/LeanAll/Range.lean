/-! Joining range lemmas: used by the generated Haar cover files to combine the per-module batch ranges
in a balanced tree instead of one large case split. -/

namespace BipartiteDD.LeanAll

theorem range_join {Q : Nat → Prop} {lo mid hi : Nat} (h1 : ∀ b, lo ≤ b → b < mid → Q b)
    (h2 : ∀ b, mid ≤ b → b < hi → Q b) : ∀ b, lo ≤ b → b < hi → Q b :=
  fun b hl hh => if h : b < mid then h1 b hl h else h2 b (Nat.le_of_not_lt h) hh

end BipartiteDD.LeanAll
