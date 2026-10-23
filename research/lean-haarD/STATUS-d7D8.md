# STATUS d7D8: Δ7·D8 record, 88,920 vertices

**Status: done.** `nb_7_8` is kernel-checked:

    theorem nb_7_8 : ∃ H : SimpleGraph (Fin 88920), BipartiteDD.IsBipartiteDegDiam H 7 8

Axioms (`lean/D7D8Axioms.out.txt`): `nb_7_8` depends only on `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `admit`, `axiom`, or `native_decide` in `lean/BipartiteDD/Haar/D7D8/`.

## The record
- Group `G = PSL(2,19) × Z13`, `|G| = 44460`, Haar graph on `G ⊕ G`, `|S| = 7`.
- `S` is `research/frontier/sols/d7D8_psl_19_13_s403.txt`. `build_haar2.py` on that file:
  `ecc = 8` from both sides, `n = 88920`, degree 7, no duplicate edges, VALID.
- Vertex count is proved: `haarVert : G ⊕ G ≃ Fin 88920`, built from the numbering `equivG : G ≃ Fin 44460`.

## Modules (`lean/BipartiteDD/Haar/D7D8/`)
- `PSL19.lean`: `PSL(2,19)` as normalised matrices (`canon` picks the sign with `posB`), a `Group` instance,
  and a closed-form numbering `enc`/`quad`/`grpP` onto `Fin 3420`. Proofs by case analysis on `c = 0`, with
  `decide` only on small finite statements (no enumeration of all 19⁴ quadruples).
- `Base.lean`: `G := PSL19.Grp × Multiplicative (ZMod 13)` (additive `Z13`), `idxG`/`gOf`, `equivG`, `haarVert`.
- `Diam8.lean`: diameter-8 lemma `ediam_le_eight_of` from three covering hypotheses (A–A and B–B of 4 pairs,
  A–B of 3 pairs), and `isBipartiteDegDiam_eight_equiv`. Reuses `colorable_of`/`degree_of` from `Haar.Main`.
- `Gens.lean`: the seven generators `sGl`.
- `Check.lean`: covering words `wAA`, `wAB`, `wBB` (base-7 codes, 8/7/8 digits), `chkList`.
- `CertAA{0..9}`, `CertAB{0..9}`, `CertBB{0..9}`: stage modules, 4446 codes each, one `decide +kernel` per stage.
  Together they cover all `44460` group elements for each of the three conditions.
- `Cover.lean`, `Covers.lean`: aggregation, and the group-level covering hypotheses `coverAA/AB/BB`.
- `Record.lean`: `nb_7_8`.
- Generator: `research/lean-haarD/d7D8/gen_d7D8.py` (Python covering words, verified for all 44460 elements; regenerates everything).

## Obstacles met and how they were resolved
1. `decide` over all `19⁴` quadruples used 6.8 GB and was killed. Replaced by case proofs.
2. Z13 was first a multiplicative `ZMod 13` factor inside `Prod`, so the certificate check failed at index 1.
   Fixed by `Multiplicative (ZMod 13)`.
3. The generator cut the code list at fixed byte offsets, giving a parse error. Fixed by whole-token lines.
4. `norm_num` leaves `7 ≤ 8` open in `ℕ∞` for the 7-step walk. Closed with `simp only [Walk.length_*]` and `exact_mod_cast`.
5. `Cover.lean` needed `Mathlib.Tactic.IntervalCases`.

## Build
- Each stage: about 3 minutes and up to about 8.7 GB resident (the kernel check of 4446 codes). Built one at a time.
- `Record` depends on all 30 stages and builds with the final lake build.

## Deviations from the brief
- **Branch.** The job said `lean-haarD-d7D8`; I pushed to the designated branch `claude/lean-haard-d7d8-a7a6ag`.
- **General lemma.** `lemma` job branch (`GraphD.lean`) does not exist on origin, so the diameter-8 lemma is local
  (`Diam8.lean`, `ediam_le_eight_of`). Once `GraphD` lands, `Diam8` can be replaced by its statement.
- **Axioms.** `lean/Axioms.lean` and `Axioms.out.txt` were not extended, because they import every record and so
  would require building the rest of the library. `lean/D7D8Axioms.lean` (with `D7D8Axioms.out.txt`) does the check.
- **`Axioms.lean` not regenerated** (see above).

## Largest stage that built
All 30 stages (4446 codes each, `n` up to 44460) built, then `Record`.
