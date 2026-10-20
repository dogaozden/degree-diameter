# Lean 9592 status (stopped at the 5 h limit; not finished)

Branch: `claude/lean-9592-brief-oz6mj8` (draft PR #112). Run started 2026-10-20 08:33 UTC.
The worker restarted during the build; the clock was at 14:09 UTC when work resumed, past the 5 h limit
(13:33 UTC), so the remaining stages were not run.

## Done (each module built alone with `lake build`, all rc=0)
- `lean/gen.py` extended: record G9592 (n=9592, d=7, D=6, K=14), `SPLIT_LEVS` (one module per stored radius,
  `Graphs/G9592_lev1..5.lean`, collected by `Graphs/G9592_levs.lean`), `LOCAL_CHUNKS` (8 vertex ranges, generic
  balanced `localRange_append` join). Regenerating G5440 gives no diff.
- Built: `Graphs.G9592` (180 s, 2.7 GB), `Graphs.G9592_lev1..5` (570 / 419 / 136 / 98 / 232 s, ~1 GB each), `levs`.
- Kernel checks passed: `Stages.G9592_loc0..loc7` (52-70 s, 5.9-7.3 GB peak each), `Stages.G9592_local` (3 s),
  `Stages.G9592_s0` (234 s, 11.7 GB peak -- near the 15 GB limit, so build it alone).

## Not done
- Kernel checks `Stages.G9592_s1` .. `s5` (not started; same shape as s0, expect ~4 min and ~12 GB each).
- The theorem `nb_7_6` (pattern of `nb_16_4` in `Records.lean`, with `check_of_chain 14 7 6`, `levs`,
  `local_ok`, and a 6-way case split `r = 0 .. 5` over `stage0 .. stage5`), the `#print axioms nb_7_6` line in
  `lean/Axioms.lean`, and the regenerated `Axioms.out.txt`.

## To resume (one module at a time, via `scripts/guarded.sh`)
`lake build BipartiteDD.Stages.G9592_s1` ... `_s5`, then add `nb_7_6` in a new module that imports
`Stages.G9592_local` and `_s0.._s5`.
