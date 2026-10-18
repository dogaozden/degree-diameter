You are extending a Lean 4 + Mathlib formalization. Work on your own for up to 4 hours; do not ask for approval. Lean checks every proof, so keep iterating on compiler errors until the build passes. Prove one lemma at a time, building after each.

## Context
Branch `claude/lean-gq4-bipartite-o5mgec` has `lean/BipartiteDD/GQ4/` (Defs, Copy, Blowup, Diam, Degree, Count, Main): a generalized quadrangle of order (q,q) plus j copies of each point of a set O meeting every line in at most one point plus m(l) copies of each line l (every point on lines of total multiplicity at most j) gives a bipartite graph of maximum degree at most q+1+j and diameter at most 4 (`GQ4.isBipartiteDegDiam`, `gq4`). Read all of it first; reuse its copy-graph and diameter lemmas.

## Task: the (s,t) version with weighted point copies
New records use a GQ of order (s,t) = (q−1, q+1) with point copies given by a weight w : P → ℕ (a point may be copied twice) and line copies by m : L → ℕ. State and prove, in new files under `lean/BipartiteDD/GQST/` (add `import BipartiteDD.GQST.Main` to `lean/BipartiteDD.lean`):

```lean
/-- A finite generalized quadrangle of order (s, t). -/
structure GQst (P L : Type*) [Membership P L] (s t : ℕ) : Prop where
  pts_on_line : ∀ l : L, Nat.card {p : P // p ∈ l} = s + 1
  lines_on_pt : ∀ p : P, Nat.card {l : L // p ∈ l} = t + 1
  one_line : ∀ (p r : P) (l m : L), p ∈ l → r ∈ l → p ∈ m → r ∈ m → p = r ∨ l = m
  gq_ax : ∀ (p : P) (l : L), p ∉ l → ∃ x : P, x ∈ l ∧ ∃ m : L, p ∈ m ∧ x ∈ m
```
- `GQST.isBipartiteDegDiam`: for `G : GQst P L s t`, `w : P → ℕ`, `m : L → ℕ`, `a b : ℕ` with `∀ l, ∑ p ∈ univ.filter (· ∈ l), w p ≤ a` and `∀ p, ∑ l ∈ univ.filter (p ∈ ·), m l ≤ b`, the copy graph on `(P ⊕ Σ p, Fin (w p)) ⊕ (L ⊕ Σ l, Fin (m l))` (a copy is adjacent to exactly the original neighbours of its vertex, as in GQ4's `blowup`) satisfies `IsBipartiteDegDiam _ (max (s + 1 + a) (t + 1 + b)) 4`.
- `gqst`: the same transported to `Fin n`, `n = Fintype.card P + Fintype.card L + ∑ p, w p + ∑ l, m l`, as `∃ H : SimpleGraph (Fin n), IsBipartiteDegDiam H (max (s + 1 + a) (t + 1 + b)) 4`.
- Show the old theorem is a special case if it is quick (`gq4` from `gqst` with s = t = q, w = j·1_O, a = b = j); skip if it takes more than 30 minutes.

## Setup and rules
`git fetch origin && git checkout -b lean-gqst origin/claude/lean-gq4-bipartite-o5mgec`; install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`), `lake exe cache get` in `lean/`. Push with `git push -u origin HEAD` and after every milestone. Do not edit GQ4/, Plus2/, Records.lean, Fast.lean, Basic.lean or graph data files. No `sorry`, `admit`, new `axiom`, `native_decide`, or checking-weakening options. At the end add the new theorems to `lean/Axioms.lean`, regenerate `lean/Axioms.out.txt` with `lake env lean Axioms.lean`, commit with a message starting `milestone:`, push.

## Final reply
What builds, total build time, the exact statements proved, the `#print axioms` lines for them, any definition change and why, and the last commit hash.
