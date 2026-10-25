# STATUS d5D7b: Δ5·D7 on 3,120 vertices (PGL(2,5) × Z_13)

**Done.** `nb_5_7_3120` builds, with `#print axioms` giving exactly `propext`, `Classical.choice`, `Quot.sound`
(`lean/BipartiteDD/Haar/D5D7b/Axioms.out.txt`). No `sorry`, `admit`, `native_decide` or `axiom` in the new files.

```
theorem nb_5_7_3120 : ∃ G : SimpleGraph (Fin 3120), BipartiteDD.IsBipartiteDegDiam G 5 7
```

Graph: Haar graph of `G = PGL(2,5) × Z_13` (order 1560) and the five-element connection set of
`research/lifts/sols/haar/hc_d5D7_pgl_5_13_s1.txt` (`mat(a,b,c,d)` is [[a,b],[c,d]] modulo scalars; `z` is the Z_13
coordinate, as in `build_haar2.py`). Vertices: `G ⊕ G ≃ Fin 3120`.

## Certificate

`research/lean-haarD/gen_d5D7b.py SOL OUTDIR` builds the group in the same numbering as Lean, computes the Haar
diameter by BFS (7, checked before writing anything), and finds, for every `g ∈ G`, a six-letter A-word
`x1⁻¹ x2 x3⁻¹ x4 x5⁻¹ x6` and a six-letter B-word `x1 x2⁻¹ x3 x4⁻¹ x5 x6⁻¹` over `S`. Each word is re-checked by
multiplication. It then emits the Lean modules. Six stage modules (260 indices each, base-5 codes, 16 bits each) are
each checked by `decide +kernel`.

## Modules (lean/BipartiteDD/Haar/D5D7b/)

| Module | Content |
|---|---|
| `PGL5.lean` | `PGL(2,5)` as normalised matrix classes, port of `Haar/PGL37.lean` (37 → 5). Numbering `enc`/`quadN`, `equiv120`. |
| `Group.lean` | `PGL(2,5) × Z_13`, index `13 * enc g + z`, `equiv1560`. Port of `PGL37Z5.lean`. |
| `Words.lean` | `wordA6`, `wordB6` (words written once for any `[Group G]`), `CoverA S`, `CoverB S` (the hypotheses of `Diam7`). |
| `Check.lean` | `sVec` (the connection set), `SS`, `wordA`/`wordB` through `wordA6`/`wordB6`, `okA`/`okB`, `chkA`/`chkB`. |
| `Stage00 … Stage05` | Certificate tables; `certA0k`, `certB0k` by `decide +kernel`. |
| `Cover.lean` | `exA`, `exB`, `cover1 : CoverA SS`, `cover2 : CoverB SS`. |
| `Record.lean` | `equiv3120`, `nb_5_7_3120`. Uses `haar_isBipartiteDegDiam7_of_equiv` from `Haar/Diam7.lean`. |
| `Axioms.lean`, `Axioms.out.txt` | `#print axioms nb_5_7_3120`. |

Build order used (one module at a time): `PGL5`, `Group`, `Words`, `Check`, `Stage00` … `Stage05`, `Cover`, `Record`,
then `lake env lean Axioms.lean`. Every build passed; the record build takes a few seconds once `Diam7` is built.

## Obstacle met and fixed

The first `Record` build timed out at `isDefEq` on the `cover1` argument (the pattern in `BRIEF.md`). The cause is the one
the brief describes: `cover1` was stated with the direct product instances of `PGL5Z13.Grp`, while the lemma uses the
`[Group G]` path. The fix was the one from `STATUS-d6D10c.md`, adapted to the literal six-letter products of
`Diam7`. The words are written once generically (`wordA6`, `wordB6`), `CoverA`/`CoverB` are defined with the lemma's
hypothesis bodies under `[Group G]`, `wordA`/`wordB` in `Check` go through `wordA6`/`wordB6`, and `cover1`/`cover2` are
stated as `CoverA SS`/`CoverB SS`. With that, the lemma application elaborates. No heartbeat option was used.

## Deviations from the brief

- The brief asks for `lean-haarD-<job>` as the branch name. The session instructions name
  `claude/haar-d5d7b-record-woe5yr`, and that is the branch used.
- The brief says master holds the Haar files. On this branch the files it names (`Diam7`, `Record416640`, `PGL37*`,
  `D7D8b`, `D7D9`, `D6D7`) are present. `master` does not contain them, so the work is built on this branch.
- `lean/Axioms.lean` (the top-level aggregate) is not changed. The per-record `Axioms.lean` and `Axioms.out.txt` in the
  directory follow the pattern of `Haar/D6D7`. Adding this record to the aggregate would import and build its whole list.

## Setup

Lean `leanprover/lean4:v4.34.1` installed with elan, then `lake exe cache get` (8908 files). The build shows only
deprecation warnings for `if_pos`/`dif_pos` in `PGL5.lean`, carried over from `PGL37.lean`.
