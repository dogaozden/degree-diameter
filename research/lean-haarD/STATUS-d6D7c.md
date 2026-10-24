# STATUS d6D7c: Δ6·D7 record, 8,880 vertices

**Status: done.** `nb_6_7_8880` is kernel-checked:

    theorem nb_6_7_8880 : ∃ G : SimpleGraph (Fin 8880), BipartiteDD.IsBipartiteDegDiam G 6 7

Axioms (`lean/BipartiteDD/Haar/D6D7c/Axioms.out.txt`): `nb_6_7_8880` depends only on `propext`,
`Classical.choice`, `Quot.sound`. No `sorry`, `admit`, `axiom`, or `native_decide` in the new files.

## The record
- Group `G = SL(2,5) × Z_37`, order 4440 (`|SL(2,5)| = 120`), Haar graph on `G ⊕ G`, `|S| = 6`.
- `S` is `research/frontier/sols/d6D7_sl_5_37_orb3f0_s2.txt` (header `6 7 sl 5 n 37 N 4440`).
- `build_haar2.py` on that file (confirms the vertex count first): `ecc = 7` from both sides, `unreached 0`,
  `n = 8880`, degree 6 everywhere, no duplicate edges, `VALID d=6 D=7 group=sl 5 x Z_37 N=4440 vertices=8880`.
- The vertex count is proved: `equiv8880 : SL5Z37.Grp ⊕ SL5Z37.Grp ≃ Fin 8880`, from `SL5Z37.equiv4440`.

## Modules (all under `lean/BipartiteDD/Haar/D6D7c/`)
- `SL5.lean` (`BipartiteDD.Haar.D6D7c.SL5`): `SL(2,5)` as matrices over `ZMod 5` with determinant 1, a `Group`
  instance, the numbering `enc`/`quad`/`grpOf` (20 elements with `c = 0`, then 100 with `c ≠ 0`), `equiv120`.
  Modelled on master's `Haar/SL31.lean`.
- `SL5Z37.lean` (`BipartiteDD.Haar.D6D7c.SL5Z37`): `SL5.Grp × Multiplicative (ZMod 37)`, the numbering
  `37 * enc g + z`, `equiv4440`. Modelled on master's `Haar/SL31Z7.lean`.
- `Check.lean`: `sVec` (the six elements of S), `sel`, `SS`, the words `wordA`, `wordB` (base-6 codes, six digits),
  `okA`, `okB`, the packed tables `codeAt`, `chkA`, `chkB`. Generated.
- `Stage00.lean … Stage04.lean`: certificate stages, 888 codes each, one `decide +kernel` per stage for A and B.
  Together they cover all 4440 elements.
- `Cover.lean`: `exA`, `exB`, the covering hypotheses `cover1`, `cover2`. Generated.
- `Record8880.lean`: `equiv8880` and `nb_6_7_8880`, via the shared `Haar/Diam7.lean` lemma
  `haar_isBipartiteDegDiam7_of_equiv` (master, unchanged).
- `Axioms.lean` and `Axioms.out.txt`.
- Generator: `research/lean-haarD/gen_d6D7c.py`, run as `python3 -I gen_d6D7c.py <sol> lean/BipartiteDD/Haar/D6D7c`.
  It checks the `SL(2,5)` numbering and the group axioms on samples, verifies every A- and B-word of all 4440
  elements by direct multiplication, and only then writes the Lean files. `SL5.lean`, `SL5Z37.lean`,
  `Record8880.lean`, `Axioms.lean` are hand-written.

## Build
- Toolchain `leanprover/lean4:v4.34.1` (elan installed into `~/.elan` in this session), `lake exe cache get`.
- Each module built alone with `lake build`, all exit 0:
  `SL5` (3 s, no warnings), `SL5Z37` (2 s), `Check` (2 s), `Stage00` … `Stage04` (about 25 s each), `Cover` (3 s),
  `Record8880` (2 s, plus its imports).
- `lake env lean BipartiteDD/Haar/D6D7c/Axioms.lean` gives the axioms line above.

## Deviations from the brief
- **Branch.** The brief said `lean-haarD-d6D7c`; the session's designated branch is `claude/d6d7c-record-8880-2pja08`,
  and that is where the work is.
- **Master axiom file.** `lean/Axioms.lean` and its `.out.txt` were not extended, because they import the whole record
  library (`GQST.Main`, `Records`, `Records9592`), which would need every one of those modules built. The job's own
  `D6D7c/Axioms.lean` does the check, as for D6D7 and D6D7b.
- **Group files.** `SL(2,5)` was not in master (`SL19`, `SL23`, `SL31`, `SL211`, `SL213` exist), so `SL5.lean` and
  `SL5Z37.lean` are new, and placed under `D6D7c/` to avoid clashing with master names.

## Largest stage that built
All five stages (888 codes each, `n` up to 4440), then `Cover`, `Record8880` and `Axioms`.
