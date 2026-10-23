# lean-haarD build check (master at 8414131)

Checked: `origin/master` at 8414131 (the three lean-haarD merges: GraphD lemma, nb_7_8, nb_6_9_haar).
Toolchain: `leanprover/lean4:v4.34.1`, Mathlib v4.34.1 from `lake exe cache get` (8,908 files, all downloaded, none compiled locally).
Build: one `lake build <Module>` per module, run sequentially. Times are wall-clock seconds from the build log.

## Result

- **All 58 new modules build** with exit 0. Their build logs contain no `sorry` and no `error` lines.
  - Haar lemma: `Haar.Main`, `Haar.GraphD`, `Haar.Diam9`, `Haar.SL23`, `Haar.SL23Z5` (5 modules, about 92 s total).
  - (6,9): `Haar.D6D9.Check`, `Stage00` to `Stage11`, `D6D9.Cover`, `Haar.Record121440` (14 modules, about 56 min).
  - (7,8): `Haar.D7D8.PSL19`, `Base`, `Gens`, `Check`, `Diam8`, `CertAA0` to `CertAA9`, `CertAB0` to `CertAB9`, `CertBB0` to `CertBB9`, `Cover`, `Covers`, `Record` (38 modules, about 75 min).
  - Driver wall time: 09:16 to 11:30 container clock (about 2 h 13 min) for these 58 modules.
- **Axioms of the new results: identical to the committed outputs.**
  - `lake env lean BipartiteDD/Haar/D6D9/Axioms.lean` gives `'nb_6_9_haar' depends on axioms: [propext, Classical.choice, Quot.sound]`, identical to `BipartiteDD/Haar/D6D9/Axioms.out.txt`.
  - `lake env lean D7D8Axioms.lean` gives the four lines for `nb_7_8`, `D7D8.coverAA`, `D7D8.card_SS` and `isBipartiteDegDiam_eight_equiv`, all `[propext, Classical.choice, Quot.sound]`, identical to `D7D8Axioms.out.txt`.
- **Root `Axioms.lean`: not yet checked.** It imports 16 modules outside the brief's list (`GQST.Main`, `Records`, `Records9592`, `SingerC.Main`, `SingerC.W3Main`, `Haar.Record2620/2640/1728/1152/1764/2662`, `GQ4.Main`, `GQ4.Count`, `ASq.Main`, `GQST.StandinMain`). Their import closure is 167 modules, of which 93 were unbuilt at the start. The status is updated below once that build finishes.

## Deviations from the brief

- **Build order.** The D7D8 Cert modules were built after `Check`, because `Check` imports `Gens`, which the Cert modules import. The brief listed `Check` after `Covers`, which would not have built in that order.
- **Parallel OOM during the `Axioms.lean` imports.** `lake build BipartiteDD.Records` ran its jobs in parallel and hit exit 137 (out of memory) in 13 places. Lake 5 has no job-limit option, so that run was stopped. The import closure is now being rebuilt strictly one module at a time, in dependency order (`lake build <Module>` for each module). The 58 modules above were all built before that step.
- **No `.lean` file changed.** The `lean/` tree was clean and equal to master throughout.

## Timings (seconds, wall)

| module | seconds |
|---|---|
| BipartiteDD.Haar.Main | 2.3 |
| BipartiteDD.Haar.GraphD | 1.3 |
| BipartiteDD.Haar.Diam9 | 4.2 |
| BipartiteDD.Haar.SL23 | 81.5 |
| BipartiteDD.Haar.SL23Z5 | 3.4 |
| BipartiteDD.Haar.D6D9.Check | 4.2 |
| BipartiteDD.Haar.D6D9.Stage00 | 251.3 |
| BipartiteDD.Haar.D6D9.Stage01 | 286.3 |
| BipartiteDD.Haar.D6D9.Stage02 | 269.8 |
| BipartiteDD.Haar.D6D9.Stage03 | 269.3 |
| BipartiteDD.Haar.D6D9.Stage04 | 286.6 |
| BipartiteDD.Haar.D6D9.Stage05 | 279.8 |
| BipartiteDD.Haar.D6D9.Stage06 | 289.3 |
| BipartiteDD.Haar.D6D9.Stage07 | 299.3 |
| BipartiteDD.Haar.D6D9.Stage08 | 292.2 |
| BipartiteDD.Haar.D6D9.Stage09 | 282.5 |
| BipartiteDD.Haar.D6D9.Stage10 | 271.4 |
| BipartiteDD.Haar.D6D9.Stage11 | 280.4 |
| BipartiteDD.Haar.D6D9.Cover | 3.9 |
| BipartiteDD.Haar.Record121440 | 4.1 |
| BipartiteDD.Haar.D7D8.PSL19 | 62.9 |
| BipartiteDD.Haar.D7D8.Base | 2.9 |
| BipartiteDD.Haar.D7D8.Gens | 2.8 |
| BipartiteDD.Haar.D7D8.Check | 2.8 |
| BipartiteDD.Haar.D7D8.Diam8 | 3.7 |
| BipartiteDD.Haar.D7D8.CertAA0 | 155.4 |
| BipartiteDD.Haar.D7D8.CertAA1 | 160.4 |
| BipartiteDD.Haar.D7D8.CertAA2 | 163.9 |
| BipartiteDD.Haar.D7D8.CertAA3 | 147.1 |
| BipartiteDD.Haar.D7D8.CertAA4 | 153.9 |
| BipartiteDD.Haar.D7D8.CertAA5 | 142.9 |
| BipartiteDD.Haar.D7D8.CertAA6 | 145.8 |
| BipartiteDD.Haar.D7D8.CertAA7 | 157.8 |
| BipartiteDD.Haar.D7D8.CertAA8 | 176.9 |
| BipartiteDD.Haar.D7D8.CertAA9 | 165.5 |
| BipartiteDD.Haar.D7D8.CertAB0 | 132.8 |
| BipartiteDD.Haar.D7D8.CertAB1 | 139.1 |
| BipartiteDD.Haar.D7D8.CertAB2 | 143.4 |
| BipartiteDD.Haar.D7D8.CertAB3 | 137.4 |
| BipartiteDD.Haar.D7D8.CertAB4 | 131.8 |
| BipartiteDD.Haar.D7D8.CertAB5 | 131.5 |
| BipartiteDD.Haar.D7D8.CertAB6 | 124.0 |
| BipartiteDD.Haar.D7D8.CertAB7 | 128.9 |
| BipartiteDD.Haar.D7D8.CertAB8 | 135.8 |
| BipartiteDD.Haar.D7D8.CertAB9 | 121.2 |
| BipartiteDD.Haar.D7D8.CertBB0 | 149.0 |
| BipartiteDD.Haar.D7D8.CertBB1 | 154.0 |
| BipartiteDD.Haar.D7D8.CertBB2 | 150.3 |
| BipartiteDD.Haar.D7D8.CertBB3 | 150.1 |
| BipartiteDD.Haar.D7D8.CertBB4 | 159.7 |
| BipartiteDD.Haar.D7D8.CertBB5 | 152.6 |
| BipartiteDD.Haar.D7D8.CertBB6 | 150.8 |
| BipartiteDD.Haar.D7D8.CertBB7 | 152.5 |
| BipartiteDD.Haar.D7D8.CertBB8 | 147.5 |
| BipartiteDD.Haar.D7D8.CertBB9 | 153.0 |
| BipartiteDD.Haar.D7D8.Cover | 9.4 |
| BipartiteDD.Haar.D7D8.Covers | 3.0 |
| BipartiteDD.Haar.D7D8.Record | 12.5 |
