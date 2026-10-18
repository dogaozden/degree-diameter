You are formalizing a theorem in Lean 4 with Mathlib. Work on your own for up to 5 hours; do not ask for approval. Lean checks every proof, so keep iterating on compiler errors until the build passes. Prove one lemma at a time, building after each.

## The theorem (informal)
Read `research/gq4/THEOREM.md` first (sections Setting, Construction, Theorem, Proof). In short: take a generalized quadrangle of order (q,q) (points P, lines L), a set O of points meeting every line in at most one point, a number j, and a multiplicity m : L → ℕ with every point on lines of total multiplicity at most j. Add j copies of each point of O (a copy is adjacent to the lines through its point) and m(l) copies of each line l (a copy is adjacent to the points of l). The resulting incidence graph is bipartite, has maximum degree at most q + 1 + j, and diameter at most 4.

The proof: (1) the incidence graph of a GQ has diameter at most 4: point–line distance ≤ 3 by the GQ axiom (for p ∉ l there is a point x ∈ l collinear with p: p – m – x – l), point–point and line–line ≤ 4 by first stepping to any incident line/point; (2) a copy has the same neighbours as its original, so it is within the original's distance of everything (and at distance 2 from the original), hence diameter stays ≤ 4; (3) degrees: an original line gains j·|O ∩ l| ≤ j neighbours, an original point gains ∑ m over its lines ≤ j, a copy has degree q + 1.

## Setup
1. `git fetch origin && git checkout -b lean-gq4 origin/master && git merge origin/research-diam4` (research-diam4 has THEOREM.md; if the merge conflicts outside `lean/`, take research-diam4's version). Push with `git push -u origin HEAD`, and push after every milestone.
2. Install elan: `curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, then `source ~/.elan/env`. In `lean/`, run `lake exe cache get`.
3. Put all new code in `lean/BipartiteDD/GQ4/` (several files are fine) and add `import BipartiteDD.GQ4.Main` to `lean/BipartiteDD.lean`. Build with `lake build BipartiteDD.GQ4.Main`. Do not edit `BipartiteDD/Basic.lean`, `Records.lean`, `Fast.lean`, `Plus2/` or the graph data files: another session changes records on a different branch.
4. Read `lean/BipartiteDD/Plus2/` first: it proves the same kind of statement for projective planes (graph on a sum type, `Colorable 2`, degree via `neighborSet ncard`, `ediam`, transport along an equivalence to `Fin n`). Reuse its patterns.

## Definitions (use these; fix only syntax errors, and report any change)
```lean
/-- A finite generalized quadrangle of order (q, q), given by its incidence relation. -/
structure GQ (P L : Type*) [Membership P L] (q : ℕ) : Prop where
  pts_on_line : ∀ l : L, Nat.card {p : P // p ∈ l} = q + 1
  lines_on_pt : ∀ p : P, Nat.card {l : L // p ∈ l} = q + 1
  one_line : ∀ (p r : P) (l m : L), p ∈ l → r ∈ l → p ∈ m → r ∈ m → p = r ∨ l = m
  gq_ax : ∀ (p : P) (l : L), p ∉ l → ∃ x : P, x ∈ l ∧ ∃ m : L, p ∈ m ∧ x ∈ m
```
(The uniqueness half of the GQ axiom is not needed for these bounds. Add `[Fintype P] [Fintype L] [DecidableEq ...]` or classical decidability where needed.)

## Statements to prove (names fixed)
- `GQ.ediam_le_four`: the plain incidence graph on `P ⊕ L` has `ediam ≤ 4` (needs `1 ≤ q + 1`, i.e. every point is on a line and every line has a point; derive these from the card axioms).
- A general twin lemma, `ediam_le_of_twins` or similar: adding vertices whose neighbourhood equals that of an existing vertex keeps `ediam ≤ D` when `D ≥ 2`. State it in whatever form fits the construction best.
- `GQ4.isBipartiteDegDiam`: for `G : GQ P L q`, `O : Finset P` with `∀ l, (O.filter (· ∈ l)).card ≤ 1`, `j : ℕ`, `m : L → ℕ` with `∀ p, ∑ l ∈ Finset.univ.filter (fun l => p ∈ l), m l ≤ j`, the copy graph on `(P ⊕ (O × Fin j)) ⊕ (L ⊕ Σ l, Fin (m l))` satisfies `IsBipartiteDegDiam _ (q + 1 + j) 4`.
- `gq4`: the same transported to `Fin n` with `n = Fintype.card P + Fintype.card L + j * O.card + ∑ l, m l`, stated as `∃ G : SimpleGraph (Fin n), IsBipartiteDegDiam G (q + 1 + j) 4`.
- Bonus only if everything above is done: `GQ.card_points : Fintype.card P = (q + 1) * (q ^ 2 + 1)` from the axioms (needs the uniqueness half; add it as an extra hypothesis if you must).

## Rules
No `sorry`, no `admit`, no new `axiom`, no `native_decide`, no options that weaken checking. Do not change `IsBipartiteDegDiam`.
At the end: add the new theorems to `lean/Axioms.lean`, run `lake env lean Axioms.lean > Axioms.out.txt`, check the new lines list only propext, Classical.choice and Quot.sound, commit with a message starting `milestone:` and push.

## Final reply
What builds, total `lake build` time, the exact statements proved (copy them), the `#print axioms` output for them, any definition you changed and why, and the commit hash of your last push.
