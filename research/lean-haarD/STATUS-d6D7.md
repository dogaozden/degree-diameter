# STATUS d6D7: Δ6·D7 record, 8,370 vertices

**Status: done.** `nb_6_7_haar` is kernel-checked:

    theorem nb_6_7_haar : ∃ G : SimpleGraph (Fin 8370), BipartiteDD.IsBipartiteDegDiam G 6 7

Axioms (`lean/BipartiteDD/Haar/D6D7/Axioms.out.txt`): `nb_6_7_haar` depends only on `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, or `native_decide` in the new files.

## The record
- Group `G = meta 279 15 7 = Z_279 ⋊ Z_15`, `(a,j)(b,l) = (a + 7^j b, j + l)`, `|G| = 4185`, Haar graph on
  `G ⊕ G`, `|S| = 6`.
- `S` is `research/frontier/sols/d6D7_meta_279_15_7_1_s1.txt`. `build_haar2.py` on that file:
  `ecc = 7` from both sides, `n = 8370`, degree 6, no duplicate edges, VALID.
- The vertex count is proved: `equiv8370 : G ⊕ G ≃ Fin 8370` from `Meta279.equivG : G ≃ Fin 4185`.

## Modules
- `lean/BipartiteDD/Haar/D6D7/Group.lean` (`Meta279`): the group as `ZMod 279 × ZMod 15` with the twist
  `7 ^ y.val`, a `Group` instance (`tw_add` by `decide +kernel` on all 225 pairs), and the numbering
  `enc g = x.val * 15 + y.val`, `grpOf n = (n / 15, n % 15)`, `equivG`.
- `lean/BipartiteDD/Haar/D6D7/Check.lean`: `S`, the words `wordA c`, `wordB c` (base-6 codes, six digits), `okA`,
  `okB`, the packed tables `codeAt` (16 bits per code), `chkA`, `chkB`.
- `lean/BipartiteDD/Haar/D6D7/Stage00–04.lean`: certificate stages, 837 codes each, one `decide +kernel` per stage
  for A and B. Together they cover all 4185 elements.
- `lean/BipartiteDD/Haar/D6D7/Cover.lean`: `exA`, `exB`, and the covering hypotheses `cover1`, `cover2`
  (`g = x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6` and `g = x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹`).
- `lean/BipartiteDD/Haar/Diam7.lean`: the odd diameter-7 lemma `ediam_le_seven_of`, with three-pair covers,
  written as `Diam9.lean` is for four pairs. Gives `haar_isBipartiteDegDiam7_of_equiv`.
- `lean/BipartiteDD/Haar/Record8370.lean`: `nb_6_7_haar`.
- `lean/BipartiteDD/Haar/D6D7/Axioms.lean` and `Axioms.out.txt`.
- Generator: `research/lean-haarD/gen_d6D7.py`. Python checks: `7^15 ≡ 1 mod 279`, group inverses and associativity
  on samples, and the A- and B-words of all 4185 elements, each re-multiplied directly.

## Build
- Each module built alone with `lake build`: `Group` (3.8 s), `Check`, `Stage00` (12 s), `Stage01–04`, `Diam7`, `Cover`,
  `Record8370`. Every build exited 0 with no errors.
- `lake env lean BipartiteDD/Haar/D6D7/Axioms.lean` gives the axioms line above.

## Deviations from the brief
- **Branch.** The job named `lean-haarD-d6D7`; the work is on the designated branch `claude/lean-haar-d6d7-kbpe9j`.
  Draft PR #238.
- **Diameter lemma.** Local to `Haar/Diam7.lean` (as `Diam9.lean` is for the four-pair case), not `GraphD`'s
  `haar_ediam_le_odd`, because the transport to `Fin 8370` is then done as in the other records.
- **Master axiom file.** `lean/Axioms.lean` and its `.out.txt` were not extended, because they import every
  record and would require building the rest of the library. The job's own `D6D7/Axioms.lean` does the check.
  This matches the D7D8 status.
- **Group check.** The group laws are proved in the `Group` instance (`ring` and `tw_add`), not by a separate
  `decide` over all triples.

## Largest stage that built
All five stages (837 codes each, `n` up to 4185) built, then `Diam7`, `Cover`, `Record8370`.
