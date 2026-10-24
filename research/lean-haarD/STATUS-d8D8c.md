# STATUS d8D8c: Δ8·D8 record, 239,904 vertices (PSL(2,17) × Z49)

**Status: done.** `nb_8_8_239904` is kernel-checked:

    theorem nb_8_8_239904 : ∃ H : SimpleGraph (Fin 239904), BipartiteDD.IsBipartiteDegDiam H 8 8

Axioms (`lean/BipartiteDD/Haar/D8D8b/Axioms.out.txt`):
`'nb_8_8_239904' depends on axioms: [propext, Classical.choice, Quot.sound]`.
The banned-token scan (`sorry`, `admit`, `native_decide`, `axiom`) of `lean/BipartiteDD/Haar/D8D8b/*.lean` is empty.

## The record
- Group `G = PSL(2,17) × Z49`, `|G| = 119952`, Haar graph on `G ⊕ G`, `|S| = 8`.
- `S` is `research/frontier/sols/d8D8_psl_17_49_orb3_s1.txt`. Vertex count is proved: `haarVert : G ⊕ G ≃ Fin 239904`,
  built from `equivG : G ≃ Fin 119952`.
- Covering: AA and BB words of length 8 (4 pairs), AB words of length 7 (3 pairs), for every element. Generated and
  re-multiplied in Python by `research/lean-haarD/d8D8b/gen_d8D8b.py` (`python3 -I gen_d8D8b.py <sol> 2448 <outdir>`
  regenerates the committed Gens, Cert and Cover files byte for byte).

## Modules (`lean/BipartiteDD/Haar/D8D8b/`)
- `PSL17.lean`: the PSL(2,17) numbering (the PSL(2,19) construction of `D7D8/PSL19` at p = 17, bounds 8 and 136).
- `Base.lean`: `G`, `idxG`/`gOf`, `equivG`, `haarVert`. `Gens.lean`: the eight generators. `Check.lean`: `wAA`, `wAB`, `wBB`, `chkList`.
- `CertAA{0..48}`, `CertAB{0..48}`, `CertBB{0..48}`: 147 stage modules, 2448 codes each, one `decide +kernel` per stage.
- `Cover.lean`, `Covers.lean`: aggregation and the group-level covering hypotheses.
- `Record.lean`: `nb_8_8_239904`. `Axioms.lean` / `Axioms.out.txt`: the axioms check.
- Reused from master, not copied: `BipartiteDD.Haar.D7D8.Diam8` (the diameter-8 lemma `isBipartiteDegDiam_eight_equiv`).

## Build
- Elan 4.2.4 installed in the sandbox; `lake exe cache get` (Mathlib v4.34.1) ok.
- `research/lean-haarD/d8D8b/build_all.sh` built `D7D8.Diam8`, the 147 stage modules, `Cover`, `Covers`, `Record`,
  one `lake build` at a time: 151 OK, no failure. Each stage about 50–65 s, about 2.5 h in total.
- `Axioms.out.txt` produced by `lake env lean` on `Axioms.lean`, exit code 0.

## Deviations from the brief
- **Branch.** The session's designated branch is `claude/haar-psl-17-49-record-d8d8c-uupxw3`, used instead of `lean-haarD-d8D8c`.
- **Start point.** Work restarted from `origin/master`. The D8D8b tree was taken from the earlier worker's branch
  `claude/haar-psl-17-49-record-y3r7u5` (commit `773b352`), then checked by regeneration and built.
- **Axioms.** `lean/Axioms.lean` was not extended, because it imports every record. The check lives in
  `Haar/D8D8b/Axioms.lean`, following the `Haar/D7D8b` pattern.
- **Theorem name.** `nb_8_8_239904` is top level, as `nb_7_8_b` is; the earlier worker's namespaced `D8D8b.nb_8_8` was renamed.

## Largest stage that built
All 147 stage modules (2448 codes each, `n` up to 119952 per side), then `Cover`, `Covers`, `Record` and `Axioms`.
