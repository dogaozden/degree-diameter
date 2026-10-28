# STATUS: projection (Gómez ΩH_q, Theorem 1 of research/squads/cells/d12D8_table.md §2)

**Verdict: done.** Everything in the card builds, with no sorry, admit or axiom, and the main theorems use only
`propext`, `Classical.choice`, `Quot.sound`.

## Files (all new, under lean/BipartiteDD/LeanMaxx/Projection/)

- `Walk.lean`: walk-level lemmas.
  - `copy_index_const`: a walk through copy vertices only keeps one copy index (from h1).
  - `newCount`: the number of new vertices a walk passes, not counting its start.
  - `exists_label_walk`: a walk from `a` to a copy vertex `b` projects to a `B`-walk from `f a` to `f b`, with
    `q.length + 2 * newCount c p + [c a new] ≤ p.length`. Induction on the walk, one edge at a time.
- `Main.lean`: the theorems.
  - `walk_ge`: for every walk from a new `x` to a copy vertex `v` of copy `j`, length ≥ `B.dist (f x) (f v) + 3`.
  - `edist_ge` (**main theorem**, name as in the card): `(B.dist (f x) (f v) + 3 : ℕ∞) ≤ G.edist x v`.
  - `dist_ge`: the Reachable version, `B.dist (f x) (f v) + 3 ≤ G.dist x v`.
  - `ediam_ge`: the corollary, `(D₁ + 3 : ℕ∞) ≤ G.ediam` when `B.edist t s = D₁`, `f x = t`, `f v = s`.
- `Axioms.lean` and `Axioms.out.txt`: `#print axioms` for `walk_ge`, `edist_ge`, `dist_ge`, `ediam_ge`.
  Output: `[propext, Classical.choice, Quot.sound]` for each.

## Statement choices (say so if you want them changed)

- The hypotheses h1, h2, h3 are written as in the card. h3 is implied by h2 (h2 already says a new vertex's
  neighbours are copy vertices), but it is kept as stated and used in the proof.
- The hypothesis `hmiss` ("x has no neighbour w with `c w = some j`") is written `∀ w, G.Adj x w → c w ≠ some j`.
- The corollary takes `B.edist t s = D₁` (a pair at distance D₁) and drops the card's "B has diameter D₁" hypothesis.
  The inequality does not use it, so the stated corollary is strictly stronger than the card's. For a connected
  `B`, such a pair always exists (the diameter is attained).
- No connectivity hypothesis on `B` or `G`. If `G` has no walk from `x` to `v`, `edist = ⊤` and the bound is trivial.
  If it has one, the projected walk shows that `B` joins `f x` and `f v`, so `B.dist` is the genuine distance.
- `walk_ge` and `dist_ge` are extra lemmas, not in the card.

## Proof outline (as formalised)

1. `exists_label_walk`: induction on the walk. A copy–copy edge is a `B`-edge (h1). A copy–new–copy pass keeps the
   label (h2) and costs 2. A walk that starts at a new vertex pays 1 for its first edge. The case new–new is
   excluded by h3.
2. `walk_ge`: the walk starts `x → u1 → …`. If no new vertex follows `x`, then `u1` and `v` lie in one copy index
   (`copy_index_const`), so `c u1 = some j`. That contradicts `hmiss`. Hence `newCount ≥ 1`, and the bound is
   `q.length + 3 ≤ p.length`. Finally `B.dist ≤ q.length` (`SimpleGraph.dist_le`).
3. `edist_ge` and `dist_ge` come from `walk_ge` by `le_iInf` and by `Reachable.exists_walk_length_eq_dist`.

## Build and check (reproduce)

    cd lean && export PATH=$HOME/.elan/bin:$PATH   # elan installed to ~/.elan; toolchain leanprover/lean4:v4.34.1
    lake exe cache get
    lake build BipartiteDD.LeanMaxx.Projection.Main
    lake build BipartiteDD.LeanMaxx.Projection.Axioms

- `grep -nE "sorry|admit|axiom|native_decide|implemented_by|extern|unsafe" lean/BipartiteDD/LeanMaxx/Projection/*.lean`:
  no hits in `Walk.lean` or `Main.lean`. In `Axioms.lean` the only hits are the `#print axioms` lines, which are
  required by the acceptance check.

## Remaining

Nothing in the card. Possible follow-up (not asked): an instance check that the hypotheses are satisfiable, e.g. the
two-copy example in the note, to show the theorem is not vacuous.
