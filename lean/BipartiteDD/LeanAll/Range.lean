/-! Joining range lemmas: used by the generated Haar cover files to combine the per-module batch ranges
in a balanced tree instead of one large case split. -/

namespace BipartiteDD.LeanAll

theorem range_join {Q : Nat → Prop} {lo mid hi : Nat} (h1 : ∀ b, lo ≤ b → b < mid → Q b)
    (h2 : ∀ b, mid ≤ b → b < hi → Q b) : ∀ b, lo ≤ b → b < hi → Q b :=
  fun b hl hh => if h : b < mid then h1 b hl h else h2 b (Nat.le_of_not_lt h) hh

theorem range_one {Q : Nat → Prop} {b : Nat} (h : Q b) : ∀ x, b ≤ x → x < b + 1 → Q x :=
  fun x h1 h2 => (Nat.le_antisymm (Nat.le_of_lt_succ h2) h1) ▸ h

end BipartiteDD.LeanAll
