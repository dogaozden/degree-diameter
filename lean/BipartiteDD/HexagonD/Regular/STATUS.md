# Theorem R instance (regular diameter 6, odd q): status

Brief: `docs/lean-thmR-brief.md` (on master). Lean files in this folder. Branch `lean-thmR2`, resumed from `lean-thmR`.

## Done (builds, no sorry/admit/axiom/native_decide; axioms only propext, Classical.choice, Quot.sound)

- **Step 1** (`Relation.lean`): the doubled and whiskered graph of `theoremD` as an explicit bipartite relation
  `levRel` between point versions `PtVer` and line versions `LnVer` (`biGraph (levRel …)`).
  - `levRel_isBipartiteDegDiam`: max degree `q + m`, diameter `≤ 6`.
  - `natCard_sides`: `|PtVer|` and `|LnVer| + (m-1)·m·q = |PtVer| + (m-1)·m·(q³+m)`.
  - `exists_levRel`: instantiated at `theoremD`'s spread line and whisker set (`theorem4`).
- **Step 2** (`Classes.lean`): `twinKey` (line, first letter, and second letter for `v` only) and `levRel_twin`.
  The class sizes are not counted as such; the count needed for step 3 is done directly on the deleted set.
- **Step 3a** (`Kept.lean`): `Dele` (line versions of height at least 2 with non-zero last letter); the kept version
  `⟨l, extStr s 0 l⟩` of a line through a point version is adjacent and never deleted (`not_dele_kept`); every
  version keeps `q + 1` neighbours after the deletion (`ncard_degR_ge`, `ncard_degL_restrict_ge`).
- **Step 3b** (`Choice.lean`): `Q` is a set of `q` lines of `InPi ∖ {v}`; `Ldel c Q` is the other `InPi` lines
  (`q³ + 1 − q` of them, including `v`); `delSet v W m (Ldel c Q)` is the `Dele` versions of those lines. Its size is
  `(m-1)·m·(q³-q+m)` (`card_delSet_eq`), which is the excess `|β| − |α|`. The twin-class condition holds because each
  class keeps a version with last letter `0` (`hclass`, `repLast`).
- **Step 3c and 4** (`Final.lean`): `regular_levRel` applies `Regular.regular_of_twin_classes` to `levRel` with
  `delSet v W m (Ldel c Q)`. The deficit bound `2·s·(Δ+s+1) < Σ deficits` uses double counting
  (`degL_restrictR_add`) with `numeric_bound` (`q ≥ 2`, `m ≥ 2`).
  - `theoremR` (`m ≥ 2`): `∃ G : SimpleGraph (Fin (2·(q+1)·(q⁴+q²+1+(m−1)(q³+m+1)))), IsBipartiteRegDiam G (q+m) 6`.
  - `theoremR_two` (`m = 2`): `∃ G : SimpleGraph (Fin (2·(q+1)·(q⁴+q³+q²+4))), IsBipartiteRegDiam G (q+2) 6`.

## Not done

- A full-library `lake build` has not been run on this branch; only the Regular modules listed in `Axioms.lean` were built.
