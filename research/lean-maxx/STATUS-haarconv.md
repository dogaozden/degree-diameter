# STATUS: haarconv (converse of the Haar covering criterion)

**Done.** All three main theorems build with no sorry, admit, axiom, native_decide, implemented_by, extern or unsafe in
our files. `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound` for each.

## Files (all new, under `lean/BipartiteDD/LeanMaxx/Haarconv/`)

- `Ball.lean` (module `BipartiteDD.LeanMaxx.Haarconv.Ball`): balls around the base vertices `(1, A) = .inl 1` and
  `(1, B) = .inr 1`, described by words (`LBall`, `RBall`), their one-step lemmas, and `exists_lBall`, `exists_rBall`.
  A walk of length `L` from `v` to the base gives `k ≤ L` with `v` in the `k`-ball. The disjunct fixes the side of `v`
  from the parity of `k`, so no parity lemma is needed.
- `Converse.lean` (module `BipartiteDD.LeanMaxx.Haarconv.Converse`): the statements below.
- `Axioms.lean` and `Axioms.out.txt`: `#print axioms` for each main theorem.

## Main theorems (namespace `BipartiteDD.LeanMaxx.HaarConv`)

- `cover_of_ediam_le_five (S : Finset G) (hS : S.Nonempty) (h : (haarGraph S).ediam ≤ 5)` concludes the two covers
  `∀ g, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a⁻¹ * b * c⁻¹ * d` and `∀ g, ∃ a ∈ S, ∃ b ∈ S, ∃ c ∈ S, ∃ d ∈ S, g = a * b⁻¹ * c * d⁻¹`.
  These are the hypotheses `hA`, `hB` of `BipartiteDD.Haar.haar_ediam_le_five`.
- `cover_of_ediam_le_even (n) (h : ediam ≤ 2 n + 2)` concludes `∀ x, ∃ s ∈ S, IsLeftWord S n (s⁻¹ * x)`, which is the
  hypothesis `hA` of `haar_ediam_le_even`.
- `cover_of_ediam_le_odd (n) (h : ediam ≤ 2 n + 1)` concludes `(∀ x, IsLeftWord S n x) ∧ (∀ x, IsRightWord S n x)`, the
  hypotheses `hA`, `hB` of `haar_ediam_le_odd`.
- Bonus: `ediam_le_five_iff (S) (hS)` gives the equivalence with `haar_ediam_le_five`.

## Choices to review

- `cover_of_ediam_le_odd` has no `S.Nonempty` hypothesis. It is not needed: an edgeless graph on `G ⊕ G` has infinite
  diameter, so `ediam ≤ 2 n + 1` already forces `S` nonempty. The statement is therefore stronger than the bare converse
  of `haar_ediam_le_odd`.
- `cover_of_ediam_le_five` keeps `hS`, as the card asks. It is used for the padding in `four_of_isLeftWord_two` and
  `four_of_isRightWord_two`: a word of at most two factors becomes four factors by repeating a factor `s`, since `s⁻¹ s = 1`.
- `IsLeftWord S n x` means at most `n` factors. With `S` nonempty this is the same as `x ∈ (S⁻¹S)^n`, because `e ∈ S⁻¹S`.
  The same holds for `IsRightWord`. So the odd converse gives Theorem 2.4(b) in the form `(S⁻¹S)^κ = G` and `(SS⁻¹)^κ = G`.
  The set-power form is not stated separately.
- The card cites `research/theorems/POLISHED.md` §9. That file is not in this repo or on branch
  `claude/thm-haar-d8-10-sf7f0a`, so I did not check the §9 wording. The statements follow `HAAR_D8_10.md` Theorem 2.4
  (read on that branch) and the hypotheses of the three sufficiency lemmas.

## How it was built

- `elan` installed with `--default-toolchain none`. `lake exe cache get` fetched the Mathlib cache (8908 files).
  Toolchain: Lean 4.34.1, Mathlib d13f23b7.
- `lake build BipartiteDD.LeanMaxx.Haarconv.Ball` and `...Converse`: both succeed in the foreground, with no warnings
  after the `ENat.coe_ne_top` → `ENat.natCast_ne_top` rename.
- `lake env lean BipartiteDD/LeanMaxx/Haarconv/Axioms.lean > Axioms.out.txt`.

## Next step

None for this card. Possible follow-ups, not started: the matching converses for `haar_ediam_le_even`/`odd` as iff
statements, and the set-power forms of the covers.
