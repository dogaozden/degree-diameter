# STATUS d7D9: Δ7·D9 record, 416,640 vertices

**Status: done.** `nb_7_9_haar` is kernel-checked:

    theorem nb_7_9_haar : ∃ G : SimpleGraph (Fin 416640), BipartiteDD.IsBipartiteDegDiam G 7 9

Axioms (`lean/BipartiteDD/Haar/D7D9/Axioms.out.txt`): `'nb_7_9_haar' depends on axioms: [propext, Classical.choice, Quot.sound]`.
No `sorry`, `admit`, `axiom` or `native_decide` in the new modules.

## The record
- Group `G = SL(2,31) × Z7`, `|G| = 208320`, Haar graph on `G ⊕ G`, `|S| = 7`.
- `S` is `research/frontier/sols/d7D9_sl_31_7_s111.txt`. `build_haar2.py` on that file: `ecc = 9` from both sides,
  `n = 416640`, degree 7, no duplicate edges, VALID.
- Vertex count is proved: `equiv416640 : SL31Z7.Grp ⊕ SL31Z7.Grp ≃ Fin 416640`, built from `equiv208320`.

## Modules (`lean/BipartiteDD/Haar/`)
- `SL31.lean`: `SL(2,31)` as matrices over `ZMod 31`, a `Group` instance, numbering `equiv29760` (`decide +kernel`
  over the triples and `List.range 29760`).
- `SL31Z7.lean`: `Grp := SL31.Grp × Multiplicative (ZMod 7)`, numbering `equiv208320`.
- `D7D9/Check.lean`: the connection set, base-7 digits, 23-bit packed codes (`codeAt`), checkers `chkA`/`chkB`.
- `D7D9/Stage00..41.lean`: 42 stage modules, 4960 indices each, both sides, `certA k`/`certB k` by `decide +kernel`.
- `D7D9/Cover.lean`: every element is an 8-letter A-word and B-word in `SS`.
- `Record416640.lean`: `nb_7_9_haar`, from `Diam9.lean` (`haar_isBipartiteDegDiam9_of_equiv`).
- `D7D9/Axioms.lean` and `Axioms.out.txt`: the axioms check.
- Generator: `research/lean-haarD/gen_d7D9.py` (covering words verified by multiplication for all 208320 elements per side).

## Build
- One module at a time. Each stage: 209–245 s, peak about 8.7 GB resident. `Check`: 12 s. `Cover`: 8 s.
  `Record416640`: 4 s. `Axioms`: 3 s.
- Full chain: `Check`, `Stage00..41`, `Cover`, `Record416640`, `Axioms`, all `rc=0`
  (`research/lean-haarD/d7D9-build-log.txt`).
- Largest stage that built: all 42 stages (4960 indices each, both sides).

## Obstacles and how they were resolved
- None blocking. The stage size (4960) was chosen from D6D9 timings and 208320 = 42 × 4960. Stage00 at 8.7 GB was the
  memory high point; no stage was killed.
- `SL31.lean` gives deprecation warnings for `dif_pos` (same pattern as `SL23.lean`); they are harmless.

## Deviations from the brief
- **Branch.** Pushed to the designated branch `claude/lean-haar-d7d9-rti0dr`, not `lean-haarD-d7D9`. Draft PR #239.
- **General lemma.** `GraphD.lean` is on master, but its certificate form needs a `List G` of every target (208320
  elements per side), which is too large for `decide`. The record uses the packed-code route of D6D9 and `Diam9.lean`.
- **Global axioms file.** `lean/Axioms.lean` and its `Axioms.out.txt` are not extended, because they import every
  record. `D7D9/Axioms.out.txt` is the record's own check, as in D6D9.
- **Not in the default library target.** `Record416640` is not imported by `BipartiteDD.lean`/`Records.lean`.
