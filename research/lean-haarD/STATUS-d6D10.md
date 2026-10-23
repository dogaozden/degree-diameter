# STATUS d6D10: Δ6·D10 506,160 in Lean

**Partial: blocked at the last step.** Everything except the record theorem and its axioms file builds, with no
`sorry`, `admit`, `native_decide` or `axiom`. `nb_6_10_haar` does **not** build yet: elaborating
`haar_isBipartiteDegDiam10_of_equiv SS equiv506160 cover` times out in `isDefEq` at the `cover` argument
(4,000,000 heartbeats, about 5 minutes). Axioms output not produced yet (`lean/BipartiteDD/Haar/D6D10/Axioms.lean`
is written but needs the record to build).

## Graph and check

- `research/frontier/build_haar2.py` on `sols/d6D10_pgl_37_5_s401.txt`: n = 506160, degree 6, diameter 10, VALID.
- Group: PGL(2,37) × Z_5, order 253080. S: the six elements of the sol file.
- Covering condition used: one nine-letter alternating cover, every g = x₁ x₂⁻¹ x₃ x₄⁻¹ x₅ x₆⁻¹ x₇ x₈⁻¹ x₉ with
  x_i ∈ S. This is the even-D criterion of `research/frontier/PLAN.md` (one condition). `Diam10.lean` proves
  diameter ≤ 10 from it (A–B distances by the cover and right-multiplication; same-side distances add one edge).
- `research/lean-haarD/gen_d6D10.py` certifies all 253080 elements, re-checking each word with the exact Lean formulas
  (`okC`, Nat arithmetic mod 37), before emitting the Lean files.

## Modules (all in `lean/BipartiteDD/Haar/`, all build)

| Module | Content |
|---|---|
| `PGL37.lean` | PGL(2,37): normal forms, group laws, numbering `Grp ≃ Fin 50616` (no `decide` over the group) |
| `PGL37Nat.lean` | Nat matrix product mod 37, normalisation, bridge `gM (prodN L) = (L.map gM).prod` |
| `PGL37Z5.lean` | product with Z_5, numbering `Grp ≃ Fin 253080` |
| `Diam10.lean` | diameter ≤ 10 from one nine-letter cover; `haar_isBipartiteDegDiam10_of_equiv` |
| `D6D10/Check.lean` | tables, `Ls`, `zW`, `okC`, `chkC` (Nat check) |
| `D6D10/Stage00..44.lean` | certificates, 5624 indices per stage (253080 = 45 · 5624), `decide +kernel` |
| `D6D10/Cover.lean` | `exC`: every index has a certificate, by the 45 stage checks |
| `D6D10/Words.lean` | `sel`, `SS`, `wordG`, `wordG_eq`, `cover` (the covering hypothesis in `PGL37Z5.Grp`) |
| `Record506160.lean` | `nb_6_10_haar`: **fails** (see obstacle) |
| `D6D10/Axioms.lean` | `#print axioms nb_6_10_haar`: not run |

## Obstacles met and how they were resolved

1. **No Lean toolchain in the container.** Installed elan and Lean v4.34.1, and ran `lake exe cache get`.
2. **Grp-level check too slow.** A Grp-level `decide` per index costs several ms per group product; 253080 indices ×
   9 letters would take about 3 hours of kernel time. The check is instead on Nat quadruples (`mN`, `normN`), and
   `PGL37Nat.lean` proves it agrees with the group (`gM_prodN`, `gM_normN`). Stage builds take about 65 s each.
3. **Stage size.** 253080 is not divisible by 5060; 45 stages of 5624 are used instead.
4. **Lean scratch files.** `UnifyTest.lean` (a diagnostic file) is not committed.

## Largest stage that built

All 45 stages build (`Stage00` … `Stage44`), each in about 65 s, serially. `Cover.lean` and `Words.lean` build too.

## Exact obstacle (open)

`Record506160.lean` line 22: `haar_isBipartiteDegDiam10_of_equiv SS equiv506160 cover` fails with
`(deterministic) timeout at isDefEq`. Tested: with `G`, `S`, `e` given explicitly, at 200k, 1M and 4M heartbeats.
Checked separately and fine (by `rfl`): `Mul` and `Inv` on `PGL37.Grp`, on `Multiplicative (ZMod 5)`, and on the
product. The two cover statements (in `Diam10.lean` and `Words.lean`) have the same parenthesisation.
Not yet tried: a concrete copy of the Diam10 lemma specialised to `PGL37Z5.Grp` (no generic `[Group G]`), so the
hypothesis and the cover elaborate to syntactically identical terms; or stating the cover with the same
`Finset`/`Group` instance path as the lemma. A trace of the `isDefEq` calls did not finish within 25 minutes.

## Deviations from the brief

- **Branch.** The brief asks for `lean-haarD-d6D10`; the session's designated branch
  `claude/lean-haar-d6d10-pz982l` is used instead. Draft PR: https://github.com/dogaozden/degree-diameter/pull/242
- **Global axioms file.** `lean/Axioms.lean` is not updated; the record's own `D6D10/Axioms.lean` is the intended output.
- **Not in the default library target.** The record is not imported by `BipartiteDD.lean`.
