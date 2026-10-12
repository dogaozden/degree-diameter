You are updating an existing Lean 4 + Mathlib proof of graph records to the newest graphs. Work on your own; do not ask for approval. Lean checks every proof, so iterate on compiler errors until the build passes.

## Context
Branch `lean-haiku` holds a Lake project in `lean/` that proves six records in strict mode: `#print axioms` lists only propext, Classical.choice and Quot.sound. `lean/gen.py` turns graph JSON files under `records/bipartite_dd/` into Lean data files, `BipartiteDD/Fast.lean` has the kernel-checkable checker, and `BipartiteDD/Records.lean` has the theorems. Read those files first.

## Task
1. `git fetch origin && git checkout lean-haiku && git merge origin/master` (master has the new graph files; take master's version of anything outside `lean/`). Push with `git push -u origin HEAD`.
2. Make the proof cover exactly these eight graphs, with these theorem names and statements (same form as now: `∃ G : SimpleGraph (Fin n), BipartiteDD.IsBipartiteDegDiam G Δ D`):

| theorem | n | Δ | D | file |
|---|---|---|---|---|
| nb_4_5 | 162 | 4 | 5 | records/bipartite_dd/d4D5/162-c-d4d5-g002-c08.json |
| nb_5_5 | 354 | 5 | 5 | records/bipartite_dd/d5D5/354-c-d5d5-w3-g014-c13.json |
| nb_7_5 | 1140 | 7 | 5 | records/bipartite_dd/d7D5/1140-spec-d7d5-g016-c15.json |
| nb_7_4 | 359 | 7 | 4 | records/bipartite_dd/d7D4/359-spec-d7d4-g017-c11.json |
| nb_11_4 | 1774 | 11 | 4 | records/bipartite_dd/d11D4/1774-spec-d11d4-g010-c19.json |
| nb_11_3 | 192 | 11 | 3 | records/bipartite_dd/d11D3/192-c-d3fam-g001-c00.json |
| nb_13_3 | 276 | 13 | 3 | records/bipartite_dd/d13D3/276-c-d3fam-g003-c19.json |
| nb_15_3 | 376 | 15 | 3 | records/bipartite_dd/d15D3/376-c-d3fam-w2-g002-c12.json |

   Update `gen.py`'s list, regenerate, delete data files no longer used (G344, G356, G1773), and update `Records.lean`, `Axioms.lean` and anything that imports them.
3. Every theorem must be kernel-checked the same way the current ones are (no `native_decide`). If one graph's kernel check takes over 30 minutes of build time after a fair try, use `native_decide` for that one only and say so.
4. Keep the sanity tests passing.
5. Rebuild everything, regenerate `lean/Axioms.out.txt` from `lake env lean Axioms.lean`, commit with a message starting `milestone:` and push.

## Rules
No `sorry`, no `admit`, no new `axiom`, no options that weaken checking. Do not change `IsBipartiteDegDiam` or `check_sound`.

## Final reply
What builds, the full `lake build` time, the per-theorem check method, the `#print axioms` output, and the commit hash of your last push.
