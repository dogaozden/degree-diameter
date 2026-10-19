# lean-all merge report

Built from `origin/research-diam4` (e80d90203). Every Lean proof from the Oct 17–19 runs is on this branch.

## Branches merged

| Branch | Tip merged | Merge commit on lean-all | Notes |
|---|---|---|---|
| `claude/lean-haar-record-iosw8s` | 83b9c9e3f | db71baa06 | Brought in `claude/lean-d5-record-theorems-th6ybb` (1a4005bf4) and `claude/lean-final-singer-c-r9xece` (cfff0e4b0) through its history. Added `Haar/*`, `nb_9_5_v3`, `nb_8_5_haar`. |
| `claude/lean-asq-bound-lk0k7y` | ff40c7f5b | 9367dcc99 | Conflict in `Axioms.lean` and `Axioms.out.txt` (both sides' imports and `#print` lines kept). Brought in `lean-gqst` (9b6c35236) through its history. |
| `lean-records2` | 1184dda93 | 1a796284d | Conflicts in `Records.lean`, `gen.py`, `Axioms.lean`, `Axioms.out.txt`, and two `Stages/*_local.lean` files. See "Conflict resolutions". |
| (fix commit, not a branch) | | f832cfc80 | Restores HEAD's `nb_9_5` and `nb_13_4` proofs under their names and adds the imports they need. |

## Branches skipped

| Branch | Tip | Reason |
|---|---|---|
| `claude/lean-d5-record-theorems-th6ybb` | 1a4005bf4 | Already an ancestor of lean-all (through the Haar merge). |
| `claude/lean-records3-graphs-6719pq` | a769200f2 | Already an ancestor of lean-all (through the Haar merge). |
| `claude/lean-final-singer-c-r9xece` | cfff0e4b0 | Already an ancestor of lean-all (through the Haar merge). |
| `lean-gqst` | 9b6c35236 | Already an ancestor of lean-all (through the ASq merge). |
| `claude/lean-gq4-bipartite-o5mgec` | 89c41e306 | Already an ancestor of lean-all (through the ASq merge). |
| `claude/lean-build-check-ctr39f`, `lean-check` | 9618ed9b1, 445fb803a | No common history with lean-all (`git merge-base` is empty; a separate Oct 12 line). A merge would conflict in about 80 files, including `Records.lean`, `Axioms.lean`, `gen.py`, and `README.md`. Every theorem name defined on the branch (118) already exists on lean-all, so nothing was dropped by skipping it. |
| `claude/lean-plus2-construction-35ci4n`, `lean-plus2` | 6d390ca48 | Same as above: no common history, about 80 conflicting files. Every theorem name it defines (116) already exists on lean-all. |
| `lean-haiku` | a0830d87f | Same as above: no common history. Every theorem name it defines (28) already exists on lean-all. |

The name check is a coverage check only. It does not compare proof bodies.

## Conflict resolutions

- **`nb_9_5` and `nb_13_4` were proved on both sides.** HEAD's proofs (through `G2510_local` and `G3122_local`) keep their names. The `lean-records2` proofs (through the `_lo`/`_hi` split) are renamed to `nb_9_5_v4` and `nb_13_4_v3`. Both statements are kept. No theorem was deleted.
- **`lean/gen.py`** kept HEAD's version (chunked local test for n > 4000). The `lean-records2` generator's `_lo`/`_hi` split is not in `gen.py`. Its generated files (`Stages/*_lo.lean`, `*_hi.lean`) are committed and are used by `nb_15_4`, `nb_16_4`, `nb_9_5_v4`, `nb_13_4_v3`. Regenerating those files needs that generator, which is not on this branch.
- **`Stages/G2510_local.lean`, `Stages/G3122_local.lean`**: `lean-records2` deleted them and HEAD kept them. Kept (HEAD's), because HEAD's `nb_9_5` and `nb_13_4` import them.
- **`lean/Axioms.lean`**: rewritten from scratch (see the axioms section). **`lean/Axioms.out.txt`**: regenerated from it.
- **`lean/BipartiteDD/Records.lean`**: union of imports from all three merges.

## Build

- `lake exe cache get` (Mathlib cache, Lean v4.34.1): ok.
- `scripts/guarded.sh 3 lake build` (the default target `BipartiteDD`): **not clean on the first pass**. Lake ran four jobs in parallel. Several kernel checks were killed by the OOM killer (exit 137) on this 15 GB machine: `G3122_local`, `G3122_hi`, `G3146_local`, `G5070_s0`–`s3`, `G5070_loc0`/`loc1`/`loc3`, `G5022_*`, `G5284_*`, `G5440_*`. Each was rebuilt alone, one `lake build <module>` at a time. Then the full default build was run again.
- Final default build: `lake build` → **BipartiteDD built, no errors** (last run 21:56 UTC, log in the session scratchpad).
- Modules outside the default target's import closure, built explicitly: `SingerC.Main`, `GQST.Main`, `GQ4.Count`, `ASq.Main`, `Haar.Record1728`, `Haar.Cert2620`, `Haar.Record2620`. `Haar.Record2620` first failed with exit 137 while a second Lean process was still running. It built after that orphan was killed.
- Wall clock: first build started 19:34 UTC; last successful build 22:14 UTC. Most of that was the sequential reruns.

## Axioms

`lean/Axioms.lean` imports the modules above and runs `#print axioms` on all 23 `nb_*` theorems (Records and Haar), on `ASq.bound`, the GQ4 and GQST copy theorems, `SingerC.Setting.propC_subspace`, and the Haar lemmas (`haar_isBipartiteDegDiam`, `haar_ediam_le_five`). Output in `lean/Axioms.out.txt`.

Result: all 45 lines list only `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no `Lean.ofReduceBool` (that would mean `native_decide`).

## Grep

`grep -rnE '\bsorry\b|\badmit\b|^\s*axiom |native_decide' lean/BipartiteDD` printed nothing (exit 1, no matches).

## Theorem list

Statements are the first line of each `theorem` in `lean/BipartiteDD/Records.lean` and `lean/BipartiteDD/Haar/Record*.lean`.

| Theorem | File | Statement (first line) |
|---|---|---|
| `nb_4_5` | `lean/BipartiteDD/Records.lean` | `theorem nb_4_5 : ∃ G : SimpleGraph (Fin 162), BipartiteDD.IsBipartiteDegDiam G 4 5 :=` |
| `nb_5_5` | `lean/BipartiteDD/Records.lean` | `theorem nb_5_5 : ∃ G : SimpleGraph (Fin 354), BipartiteDD.IsBipartiteDegDiam G 5 5 :=` |
| `nb_7_5` | `lean/BipartiteDD/Records.lean` | `theorem nb_7_5 : ∃ G : SimpleGraph (Fin 1140), BipartiteDD.IsBipartiteDegDiam G 7 5 :=` |
| `nb_7_4` | `lean/BipartiteDD/Records.lean` | `theorem nb_7_4 : ∃ G : SimpleGraph (Fin 359), BipartiteDD.IsBipartiteDegDiam G 7 4 :=` |
| `nb_11_4` | `lean/BipartiteDD/Records.lean` | `theorem nb_11_4 : ∃ G : SimpleGraph (Fin 1774), BipartiteDD.IsBipartiteDegDiam G 11 4 :=` |
| `nb_11_3` | `lean/BipartiteDD/Records.lean` | `theorem nb_11_3 : ∃ G : SimpleGraph (Fin 192), BipartiteDD.IsBipartiteDegDiam G 11 3 :=` |
| `nb_13_3` | `lean/BipartiteDD/Records.lean` | `theorem nb_13_3 : ∃ G : SimpleGraph (Fin 276), BipartiteDD.IsBipartiteDegDiam G 13 3 :=` |
| `nb_15_3` | `lean/BipartiteDD/Records.lean` | `theorem nb_15_3 : ∃ G : SimpleGraph (Fin 376), BipartiteDD.IsBipartiteDegDiam G 15 3 :=` |
| `nb_9_5` | `lean/BipartiteDD/Records.lean` | `theorem nb_9_5 : ∃ G : SimpleGraph (Fin 2510), BipartiteDD.IsBipartiteDegDiam G 9 5 :=` |
| `nb_13_4` | `lean/BipartiteDD/Records.lean` | `theorem nb_13_4 : ∃ G : SimpleGraph (Fin 3122), BipartiteDD.IsBipartiteDegDiam G 13 4 :=` |
| `nb_9_5_v4` | `lean/BipartiteDD/Records.lean` | `theorem nb_9_5_v4 : ∃ G : SimpleGraph (Fin 2510), BipartiteDD.IsBipartiteDegDiam G 9 5 :=` |
| `nb_13_4_v3` | `lean/BipartiteDD/Records.lean` | `theorem nb_13_4_v3 : ∃ G : SimpleGraph (Fin 3122), BipartiteDD.IsBipartiteDegDiam G 13 4 :=` |
| `nb_11_4_v2` | `lean/BipartiteDD/Records.lean` | `theorem nb_11_4_v2 : ∃ G : SimpleGraph (Fin 1782), BipartiteDD.IsBipartiteDegDiam G 11 4 :=` |
| `nb_13_4_v2` | `lean/BipartiteDD/Records.lean` | `theorem nb_13_4_v2 : ∃ G : SimpleGraph (Fin 3146), BipartiteDD.IsBipartiteDegDiam G 13 4 :=` |
| `nb_15_4_v2` | `lean/BipartiteDD/Records.lean` | `theorem nb_15_4_v2 : ∃ G : SimpleGraph (Fin 5070), BipartiteDD.IsBipartiteDegDiam G 15 4 :=` |
| `nb_16_4_v2` | `lean/BipartiteDD/Records.lean` | `theorem nb_16_4_v2 : ∃ G : SimpleGraph (Fin 5440), BipartiteDD.IsBipartiteDegDiam G 16 4 :=` |
| `nb_16_3` | `lean/BipartiteDD/Records.lean` | `theorem nb_16_3 : ∃ G : SimpleGraph (Fin 396), BipartiteDD.IsBipartiteDegDiam G 16 3 :=` |
| `nb_8_5` | `lean/BipartiteDD/Records.lean` | `theorem nb_8_5 : ∃ G : SimpleGraph (Fin 1728), BipartiteDD.IsBipartiteDegDiam G 8 5 :=` |
| `nb_9_5_v2` | `lean/BipartiteDD/Records.lean` | `theorem nb_9_5_v2 : ∃ G : SimpleGraph (Fin 2530), BipartiteDD.IsBipartiteDegDiam G 9 5 :=` |
| `nb_15_4` | `lean/BipartiteDD/Records.lean` | `theorem nb_15_4 : ∃ G : SimpleGraph (Fin 5022), BipartiteDD.IsBipartiteDegDiam G 15 4 :=` |
| `nb_16_4` | `lean/BipartiteDD/Records.lean` | `theorem nb_16_4 : ∃ G : SimpleGraph (Fin 5284), BipartiteDD.IsBipartiteDegDiam G 16 4 :=` |
| `nb_8_5_haar` | `lean/BipartiteDD/Haar/Record1728.lean` | `theorem nb_8_5_haar : ∃ G : SimpleGraph (Fin 1728), BipartiteDD.IsBipartiteDegDiam G 8 5 := by` |
| `nb_9_5_v3` | `lean/BipartiteDD/Haar/Record2620.lean` | `theorem nb_9_5_v3 : ∃ G : SimpleGraph (Fin 2620), BipartiteDD.IsBipartiteDegDiam G 9 5 := by` |
