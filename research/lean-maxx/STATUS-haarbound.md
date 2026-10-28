# leanmaxx-haarbound: status

Card: "haarbound", Theorem 4.1 of `research/theorems/HAAR_D8_10.md` (branch `claude/thm-haar-d8-10-sf7f0a`, §4.1):
for a finite group `G` and `S : Finset G` with `S.card = Δ ≥ 2`, if `H(G, S)` (`lean/BipartiteDD/Haar/Graph.lean`) has
`ediam ≤ D`, then `Fintype.card G ≤ ∑ j ∈ Finset.range D, (Δ - 1) ^ j`.

## Done

**Theorem 4.1 (the card) is proved, and its statement is the card's statement. Theorem 4.3 (the optional
"if time remains" item) is also proved, as stated in the note.**

- Theorem 4.3: `BipartiteDD.LeanMaxx.HaarBound.abelianization_card_le`
  (`lean/BipartiteDD/LeanMaxx/Haarbound/Abelian.lean`). Statement:
  `Nat.card (Abelianization G) ≤ Nat.card {c : Fin Δ → ℤ // ∑ i, c i = (if D % 2 = 0 then 1 else 0) ∧ ∑ i, |c i| ≤ D - 1}`
  for `S : Finset G` with `S.card = Δ` and `(haarGraph S).ediam ≤ D`. `Abelianization G` is `G / G'`. The count
  `A(Δ, D)` is the note's, indexed by `Fin Δ`; the proof transfers from the letters of `S` by an equivalence.
  No `Fintype G` or `DecidableEq G` hypothesis is needed. Corollary 4.4 and Theorems 4.5, 4.6 are not in the card
  and were not attempted.

- Main theorem: `BipartiteDD.LeanMaxx.HaarBound.card_le`
  (`lean/BipartiteDD/LeanMaxx/Haarbound/Main.lean`). Hypotheses: `[Fintype G]`, `S : Finset G`, `hS : S.card = Δ`,
  `hΔ : 2 ≤ Δ`, `hdiam : (haarGraph S).ediam ≤ D`. Conclusion as on the card. No extra hypothesis (`DecidableEq` is
  supplied by `classical` inside the proof).
- Build: `lake build BipartiteDD.LeanMaxx.Haarbound.Main` and `...Abelian` succeed with no `sorry`. `Main` has no
  warnings; `Abelian` has only deprecation warnings (`if_pos`, `if_neg`).
- Axioms: `lean/BipartiteDD/LeanMaxx/Haarbound/Axioms.out.txt`. `card_le`, `abelianization_card_le` and the
  supporting lemmas depend on `[propext, Classical.choice, Quot.sound]` only.
- Grep: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` in `Sphere.lean`,
  `Arith.lean`, `Main.lean` or `Abelian.lean`. The only `axiom` text is in `Axioms.lean`, which is the `#print axioms`
  file.

### Files (all new, additive; no existing file was edited)

| file | contents |
|---|---|
| `Sphere.lean` | `sphere H v L` (vertices at distance exactly `L`); the layer bound `|S_{m+1}(v)| ≤ Δ (Δ-1)^m` for any graph of max degree `Δ`. Proof: each vertex at distance `m+2` has a parent at distance `m+1`, and each layer vertex has its own parent at distance `m`, so it has at most `Δ-1` children. |
| `Arith.lean` | `bnd k L` (the layer bound with `k = Δ-1`), `parSum k D` (sum over `L < D` with `L ≡ D-1 mod 2`), and `parSum k D = ∑_{j<D} k^j` (telescoping `Δ(Δ-1)^{L-1} = k^L + k^{L-1}`, by induction in steps of 2). |
| `Main.lean` | Haar degree bound `≤ |S|`; bipartiteness by walk induction (a walk has even length iff its ends are on the same side); `exists_far_walk`: every far-side vertex lies at distance `m < D` with `m ≡ D-1 (mod 2)` from `(e,A)`; assembly `|G| ≤ ∑ bnd = ∑_{j<D} (Δ-1)^j`. |
| `Abelian.lean` | Theorem 4.3. The walk invariant: a walk from `(e,A)` to `w` gives an exponent vector `e` on the letters of `S` with `∑|e| ≤ length`, signed sum `sgn · [length odd]`, and `vq w = vq(e,A) · ∏ φ(s)^{e s}` in `Abelianization G`. Surjectivity onto `G/G'` comes from the far-vertex walks; finiteness from `|e s| ≤ D-1`. |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms` for `card_le`, `abelianization_card_le` and the lemmas they use. |

### Proof strategy (matches the note)

The note counts, for `D` even, the B-side vertices at odd distance `≤ D-1` from `(e,A)`, and for `D` odd the A-side
vertices at even distance `≤ D-1`. Layer `L` has at most `Δ(Δ-1)^{L-1}` vertices, and these layer bounds sum to
`∑_{j<D}(Δ-1)^j`. The formal proof is the same argument, with the far side chosen as `inl x` when `D` is odd and
`inr x` when `D` is even. Only `|S| = Δ` and degree `≤ Δ` are used. The hypothesis `2 ≤ Δ` is on the card and is not
needed by the argument (it also holds for `Δ = 1`), so it is kept but unused.

### Notes for review

- Branch: the card names `claude/leanmaxx-haarbound-<anything>`, but the session's designated branch is
  `claude/haarbound-moore-bound-qvdupi`. The work is on the designated branch.
- Theorem 4.3 proves the bound for every `D` (the note states `D ≥ 2`; the argument does not need it).
- Toolchain: Lean 4.34.1 (`elan` install, `lake exe cache get` ran). `Mathlib.Tactic.Omega` does not exist in this
  Mathlib; `omega` is core, so no import is needed.

## Partial / not done

- Corollary 4.2 (strictness) is cited in the note and was skipped, as the card says.
- Corollary 4.4 (abelian, `Q × Z_n`, metacyclic cases), Proposition 4.5 and Proposition 4.6 are not part of the card
  and were not attempted.

## Blocked

None.
