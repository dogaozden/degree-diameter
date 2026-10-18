You are extending an existing Lean 4 + Mathlib proof of graph records with four new graphs. Work on your own for up to 5 hours; do not ask for approval. Lean checks every proof, so iterate on compiler errors until the build passes.

## Context
`lean/` on master proves eight records in strict mode (`#print axioms` lists only propext, Classical.choice and Quot.sound). `lean/gen.py` turns graph JSON files under `records/bipartite_dd/` into Lean data files under `lean/BipartiteDD/Graphs/`, `BipartiteDD/Fast.lean` has the kernel-checkable checker, and `BipartiteDD/Records.lean` has the theorems. Read those files first, and `lean/CHECK.txt` for how the current build was timed.

## Task
1. `git fetch origin && git checkout -b lean-records2 origin/master && git merge origin/research-diam4` (research-diam4 has the new graph files; if the merge conflicts outside `lean/`, take research-diam4's version). Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`), then in `lean/` run `lake exe cache get`. Push with `git push -u origin HEAD`, and push after every milestone.
2. Keep the eight existing theorems unchanged and add these four, in the same form (`∃ G : SimpleGraph (Fin n), BipartiteDD.IsBipartiteDegDiam G Δ D`):

| theorem | n | Δ | D | file |
|---|---|---|---|---|
| nb_9_5 | 2510 | 9 | 5 | records/bipartite_dd/d9D5/2510-c2-d9d5-g005-c10.json |
| nb_13_4 | 3122 | 13 | 4 | records/bipartite_dd/d13D4/3122-gq4-gq4_q11_n3122.json |
| nb_15_4 | 5022 | 15 | 4 | records/bipartite_dd/d15D4/5022-gq4-gq4_q13_n5022.json |
| nb_16_4 | 5284 | 16 | 4 | records/bipartite_dd/d16D4/5284-gq4-gq4_q13_j2_n5284.json |

   Add them to `gen.py`'s list, regenerate, and update `Records.lean`, `Axioms.lean` and anything that imports them. Start with nb_9_5 and nb_13_4, commit and push, then the two 5000-vertex graphs.
3. Every theorem must be kernel-checked the same way the current ones are (no `native_decide`). These graphs are 1.5 to 3 times larger than the largest current one (1774 vertices), and the diameter check grows faster than linearly. If a graph's kernel check runs over 60 minutes after a fair try (for example splitting the check into chunks of start vertices, each its own theorem, then combining), use `native_decide` for that graph only, keep it in a separate theorem name with suffix `_native`, and say so. Do not change `IsBipartiteDegDiam` or `check_sound`.
4. Keep the sanity tests passing.
5. Rebuild everything, regenerate `lean/Axioms.out.txt` from `lake env lean Axioms.lean`, commit with a message starting `milestone:` and push.

## Rules
No `sorry`, no `admit`, no new `axiom`, no options that weaken checking. Do not touch `lean/BipartiteDD/Plus2/` or `lean/BipartiteDD/GQ4/` (another session works there).

## Final reply
What builds, the full `lake build` time, the per-theorem check method and time, the `#print axioms` output, and the commit hash of your last push.
