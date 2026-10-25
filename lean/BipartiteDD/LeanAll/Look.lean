import BipartiteDD.Fast

/-! The leaf lookup `look` used by the data files of `LeanAll.Orbit2` (kept apart so that data modules do not
depend on the checker). -/

namespace BipartiteDD.LeanAll.Orbit2

open BipartiteDD.Fast

/-- Leaf lookup by `Tree.rec`: at a node of depth `k`, bit `k - 1` of `i` picks the side (no subtraction, no
`if`). On a tree of depth `k` the leaf reached is the one at position `i % 2 ^ k`. -/
noncomputable def look {α : Type} (t : Tree α) (k i : ℕ) : α :=
  Tree.rec (motive := fun _ => ℕ → ℕ → α) (fun x _ _ => x)
    (fun _ _ ihl ihr k i =>
      cond (Nat.beq (Nat.land (Nat.shiftRight i (Nat.sub k 1)) 1) 0) (ihl (Nat.sub k 1) i)
        (ihr (Nat.sub k 1) i)) t k i

end BipartiteDD.LeanAll.Orbit2
