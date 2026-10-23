# STATUS d6D7b: Δ6·D7 record, 8,440 vertices

**Status: done.** `nb_6_7_haar_8440` is kernel-checked:

    theorem nb_6_7_haar_8440 : ∃ G : SimpleGraph (Fin 8440), BipartiteDD.IsBipartiteDegDiam G 6 7

Axioms (`lean/BipartiteDD/Haar/D6D7b/Axioms.out.txt`): `nb_6_7_haar_8440` depends only on `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, or `native_decide` in the new files.

## The record
- Group `G = meta 844 5 477 = Z_844 ⋊ Z_5`, `(a,j)(b,l) = (a + 477^j b, j + l)`, `|G| = 4220`, Haar graph on
  `G ⊕ G`, `|S| = 6`. `477^5 ≡ 1 mod 844`.
- `S` is `research/frontier/sols/d6D7_meta_844_5_477_1_s401.txt` (the file named in the job, `_s1`, does not exist;
  `_s401` is the only sol file for this group, and its header is `6 7 meta 844 5 477 n 1 N 4220`).
- `build_haar2.py` on that file: `ecc = 7` from both sides, `unreached 0`, `n = 8440`, degree 6 everywhere,
  no duplicate edges, `VALID d=6 D=7 group=meta 844 5 477 x Z_1 N=4220 vertices=8440`.
- The vertex count is proved: `equiv8440 : Grp ⊕ Grp ≃ Fin 8440` from `Meta844.equivG : Grp ≃ Fin 4220`.

## Modules (all under `lean/BipartiteDD/Haar/D6D7b/`)
- `Group.lean` (`Meta844`): the group as `ZMod 844 × ZMod 5` with the twist `477 ^ y.val`, a `Group` instance
  (`tw_add` by `decide +kernel` on all 25 pairs), the numbering `enc g = x.val * 5 + y.val`, `grpOf`, `equivG`.
- `Check.lean`: `sVec`, `sel`, `SS`, the words `wordA`, `wordB` (base-6 codes, six digits), `okA`, `okB`, the packed
  tables `codeAt` (16 bits per code), `chkA`, `chkB`. Generated, including `sVec`.
- `Stage00.lean … Stage04.lean`: certificate stages, 844 codes each, one `decide +kernel` per stage for A and B.
  Together they cover all 4220 elements.
- `Cover.lean`: `exA`, `exB`, and the covering hypotheses `cover1`, `cover2`.
- `Record8440.lean`: `equiv8440` and `nb_6_7_haar_8440`, via the shared `Haar/Diam7.lean` lemma
  `haar_isBipartiteDegDiam7_of_equiv` (master, unchanged).
- `Axioms.lean` and `Axioms.out.txt`.
- Generator: `research/lean-haarD/gen_d6D7b.py`, run as `python3 -I gen_d6D7b.py <sol> lean/BipartiteDD/Haar/D6D7b`.
  It verifies every A- and B-word of all 4220 elements by direct multiplication before writing the Lean.

## Build
- Toolchain: `leanprover/lean4:v4.34.1` (elan installed in the session), `lake exe cache get` (about 2 min).
- Each module built alone with `lake build`, all exit 0 with no errors or warnings:
  `Group` (2.3 s), `Check` (2.2 s), `Stage00` (12 s), `Stage01` (12 s), `Stage02` (13 s), `Stage03` (12 s),
  `Stage04` (16 s), `Cover` (4 s), `Record8440` (12 s).
- `lake env lean BipartiteDD/Haar/D6D7b/Axioms.lean` gives the axioms line above.

## Deviations from the brief
- **Branch.** The brief said `lean-haarD-d6D7b`; the session's designated branch is `claude/lean-haar-d6d7b-wiuw5t`,
  and that is where the work is.
- **Sol file.** `…_meta_844_5_477_1_s1.txt` does not exist; the job's file is `…_s401.txt`, used as is.
- **Theorem name.** `nb_6_7_haar` is already the 8370 record (`Record8370.lean`), so the new theorem is
  `nb_6_7_haar_8440`.
- **Master axiom file.** `lean/Axioms.lean` and its `.out.txt` were not extended, because they import every record and
  would require building the rest of the library. The job's own `D6D7b/Axioms.lean` does the check, as for D6D7.
- **Diameter lemma.** Shared, from master's `Haar/Diam7.lean`; nothing new was added to it.

## Largest stage that built
All five stages (844 codes each, `n` up to 4220), then `Cover` and `Record8440`.
