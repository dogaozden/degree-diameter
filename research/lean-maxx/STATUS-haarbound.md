# leanmaxx-haarbound: status

Card: "haarbound", Theorem 4.1 of `research/theorems/HAAR_D8_10.md` (branch `claude/thm-haar-d8-10-sf7f0a`, §4.1):
for a finite group `G` and `S : Finset G` with `S.card = Δ ≥ 2`, if `H(G, S)` (`lean/BipartiteDD/Haar/Graph.lean`) has
`ediam ≤ D`, then `Fintype.card G ≤ ∑ j ∈ Finset.range D, (Δ - 1) ^ j`.

## Done

**Theorem 4.1 is proved, and its statement is the card's statement.**

- Main theorem: `BipartiteDD.LeanMaxx.HaarBound.card_le`
  (`lean/BipartiteDD/LeanMaxx/Haarbound/Main.lean`). Hypotheses: `[Fintype G]`, `S : Finset G`, `hS : S.card = Δ`,
  `hΔ : 2 ≤ Δ`, `hdiam : (haarGraph S).ediam ≤ D`. Conclusion as on the card. No extra hypothesis (`DecidableEq` is
  supplied by `classical` inside the proof).
- Build: `lake build BipartiteDD.LeanMaxx.Haarbound.Main` succeeds with no warnings and no `sorry`.
- Axioms: `lean/BipartiteDD/LeanMaxx/Haarbound/Axioms.out.txt`. `card_le` depends on
  `[propext, Classical.choice, Quot.sound]` (the same holds for `card_sphere_le` and `parSum_eq`).
- Grep: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` in `Sphere.lean`,
  `Arith.lean` or `Main.lean`. The only `axiom` text is in `Axioms.lean`, which is the `#print axioms` file.

### Files (all new, additive; no existing file was edited)

| file | contents |
|---|---|
| `Sphere.lean` | `sphere H v L` (vertices at distance exactly `L`); the layer bound `|S_{m+1}(v)| ≤ Δ (Δ-1)^m` for any graph of max degree `Δ`. Proof: each vertex at distance `m+2` has a parent at distance `m+1`, and each layer vertex has its own parent at distance `m`, so it has at most `Δ-1` children. |
| `Arith.lean` | `bnd k L` (the layer bound with `k = Δ-1`), `parSum k D` (sum over `L < D` with `L ≡ D-1 mod 2`), and `parSum k D = ∑_{j<D} k^j` (telescoping `Δ(Δ-1)^{L-1} = k^L + k^{L-1}`, by induction in steps of 2). |
| `Main.lean` | Haar degree bound `≤ |S|`; bipartiteness by walk induction (a walk has even length iff its ends are on the same side); covering: every far-side vertex lies at distance `m < D` with `m ≡ D-1 (mod 2)` from `(e,A)`; assembly `|G| ≤ ∑ bnd = ∑_{j<D} (Δ-1)^j`. |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` for `card_le`, `card_sphere_le`, `parSum_eq`. |

### Proof strategy (matches the note)

The note counts, for `D` even, the B-side vertices at odd distance `≤ D-1` from `(e,A)`, and for `D` odd the A-side
vertices at even distance `≤ D-1`. Layer `L` has at most `Δ(Δ-1)^{L-1}` vertices, and these layer bounds sum to
`∑_{j<D}(Δ-1)^j`. The formal proof is the same argument, with the far side chosen as `inl x` when `D` is odd and
`inr x` when `D` is even. Only `|S| = Δ` and degree `≤ Δ` are used. The hypothesis `2 ≤ Δ` is on the card and is not
needed by the argument (it also holds for `Δ = 1`), so it is kept but unused.

### Notes for review

- Branch: the card names `claude/leanmaxx-haarbound-<anything>`, but the session's designated branch is
  `claude/haarbound-moore-bound-qvdupi`. The work is on the designated branch.
- Toolchain: Lean 4.34.1 (`elan` install, `lake exe cache get` ran). `Mathlib.Tactic.Omega` does not exist in this
  Mathlib; `omega` is core, so no import is needed.

## Partial / not done

- **Theorem 4.3 (abelianization bound, `|G/G'| ≤ A(Δ,D)`)**: not started at the time of this note; see the update below
  if it is present.
- Corollary 4.2 (strictness) is cited in the note and was skipped, as the card says.
- Theorems 4.4, 4.5, 4.6 and Corollary 4.4 are not part of the card.

## Blocked

None.
