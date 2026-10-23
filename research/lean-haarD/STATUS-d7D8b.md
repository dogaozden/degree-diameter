# STATUS d7D8b: Δ7·D8 record, 95,760 vertices (PSL(2,19) × Z14)

**Status: done.** `nb_7_8_b` is kernel-checked:

    theorem nb_7_8_b : ∃ H : SimpleGraph (Fin 95760), BipartiteDD.IsBipartiteDegDiam H 7 8

Axioms (`lean/BipartiteDD/Haar/D7D8b/Axioms.out.txt`): `nb_7_8_b` depends only on `propext`, `Classical.choice`,
`Quot.sound`. The banned-token scan (`sorry`, `admit`, `native_decide`, `axiom`) of `lean/BipartiteDD/Haar/D7D8b/*.lean`
is empty.

## The record
- Group `G = PSL(2,19) × Z14`, `|G| = 47880`, Haar graph on `G ⊕ G`, `|S| = 7`.
- `S` is `research/frontier/sols/d7D8_psl_19_14_orb3_s1.txt`. `build_haar2.py` on that file:
  `ecc = 8` from both sides, `n = 95760`, degree 7, 335160 edges, no duplicate edges, VALID.
- Vertex count is proved: `haarVert : G ⊕ G ≃ Fin 95760`, built from `equivG : G ≃ Fin 47880`.

## Modules (`lean/BipartiteDD/Haar/D7D8b/`)
- `Base.lean`: `G := PSL19.Grp × Multiplicative (ZMod 14)`, the numbering `idxG`/`gOf`, `equivG`, `haarVert`.
- `Gens.lean`: the seven generators `sGl`. `Check.lean`: covering words `wAA`, `wAB`, `wBB` and `chkList`.
- `CertAA{0..9}`, `CertAB{0..9}`, `CertBB{0..9}`: 30 stage modules, 4788 codes each, one `decide +kernel` per stage.
- `Cover.lean`, `Covers.lean`: aggregation and the group-level covering hypotheses.
- `Record.lean`: `nb_7_8_b`. `Axioms.lean` / `Axioms.out.txt`: the axioms check.
- Reused from master, not copied: `BipartiteDD.Haar.D7D8.PSL19` (the group) and `BipartiteDD.Haar.D7D8.Diam8`
  (the diameter-8 lemma `ediam_le_eight_of`, shared with the 88,920 record).
- Generator: `research/lean-haarD/d7D8b/gen_d7D8b.py` (covering words verified for all 47880 elements).
  Driver: `research/lean-haarD/d7D8b/build_stages.sh`, which builds one module at a time under `scripts/guarded.sh`.

## Build
- `lake exe cache get` (Mathlib v4.34.1): ok. Elan 4.2.4 and the toolchain were installed in the sandbox first.
- Each stage about 2–2.5 minutes. Built one at a time; observed about 7 GB resident during a stage.
- The full sequence (PSL19, Main, Diam8, Check, 30 stages, Cover, Covers, Record, Axioms) finished with rc=0 at
  19:41 UTC. Warnings come only from the reused `D7D8` modules (deprecated `if_pos`/`dif_pos` in `PSL19`, an unused
  variable in `Diam8`). None come from the new files.

## Deviations from the brief
- **Branch.** The brief said `lean-haarD-d7D8b`. The session's designated branch is `claude/d7d8b-psl-19-14-haar-x2cuc1`, and that is where this was pushed.
- **Theorem name.** `nb_7_8` already exists (the 88,920 record, `D7D8/Record.lean`), so the new theorem is `nb_7_8_b`.
- **Reuse.** `PSL19` and `Diam8` are imported from `D7D8` instead of copied, so no declaration is duplicated.
- **Axioms.** `lean/Axioms.lean` was not extended, because it imports every record. The check lives in
  `Haar/D7D8b/Axioms.lean`, following the `Haar/D6D7` pattern.

## Largest stage that built
All 30 stages (4788 codes each, `n` up to 47880), then `Cover`, `Covers`, `Record` and `Axioms`.
