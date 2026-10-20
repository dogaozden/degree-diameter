# Theorem R instance (regular diameter 6, odd q): status

Brief: `docs/lean-thmR-brief.md` (on master). Lean files in this folder.

## Done (builds, no sorry/admit/axiom/native_decide; axioms only propext, Classical.choice, Quot.sound)

- **Step 1** (`Relation.lean`): the doubled and whiskered graph of `theoremD` as an explicit bipartite relation
  `levRel` between point versions `PtVer` and line versions `LnVer` (`biGraph (levRel …)`).
  - `levRel_isBipartiteDegDiam`: max degree `q + m`, diameter `≤ 6`.
  - `natCard_sides`: `|PtVer| = (q+1)(q⁴+q²+1) + (m-1)(q+1)(q³+m+1)` and
    `|LnVer| + (m-1)·m·q = |PtVer| + (m-1)·m·(q³+m)` (equivalent to `|β| - |α| = (m-1)m(q³-q+m)`) for `|W| = q⁴-q²`.
  - `exists_levRel`: instantiated at `theoremD`'s spread line and whisker set (`theorem4`).
- **Step 2, partly** (`Classes.lean`): `twinKey` (line, first letter, and second letter for `v` only) and
  `levRel_twin`: versions with equal key have equal neighbourhoods. This is the `hcls` hypothesis of
  `regular_of_twin_classes`.

## Not done

- **Step 2, counts**: the fibres of `twinKey` (size `m` for `mq³+m²` keys, size `1` otherwise) are not counted.
- **Step 3** (degree deficits and the choice of `S`): not started. It needs exact degree formulas for every point
  and line version of the levelled graph (degree of `p^s` is `Σ_{ℓ ∋ p} m^{h(ℓ) - min(h(p), h(ℓ))}`), the
  choice of `S` (`(m-1)m(q³-q+m)` deleted line versions, at most `m-1` per twin class) with the per-vertex deficit
  bounds `≤ m-1`, and the bound `2s(Δ+s+1) < Σ deficits` with `T ≥ (m-1)m q²(q²-1)`.
- **Step 4** (`theoremR`): depends on step 3.

## Notes

- The brief's `|β| - |α|` is stated here in additive form to avoid natural-number subtraction.
- `Classes.lean` relies on: a point version has height at most 2 (`ht_pt_le`), and a point on `v` and a point on
  another line of height ≥ 2 cannot coincide (`existsUnique_sline`).
