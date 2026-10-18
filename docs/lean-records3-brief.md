You are extending an existing Lean 4 + Mathlib proof of graph records with four new graphs. Work on your own for up to 5 hours; do not ask for approval. Lean checks every proof, so iterate on compiler errors until the build passes.

## Context
Branch `lean-records2` proves records in strict mode, including nb_9_5 (2510 vertices) and nb_13_4 (3122) via a staged kernel check: `lean/BipartiteDD/Staged.lean` splits the distance check by radius, `lean/gen.py` writes graph data and stage modules for graphs listed in STAGED, and `check_of_chain` gives the same conclusion as `check_of_fast`. Read the last commit message of lean-records2, Staged.lean, gen.py, Records.lean and lean/CHECK.txt first.

## Task
1. `git fetch origin && git checkout -b lean-records3 origin/lean-records2 && git merge origin/research-diam4` (research-diam4 has the new graph files; on conflicts outside lean/, take research-diam4's version; inside lean/, keep lean-records2's). Install elan (`curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none`, `source ~/.elan/env`), then `lake exe cache get` in lean/. Push with `git push -u origin HEAD` and after every milestone.
2. Add these four theorems, same form (`∃ G : SimpleGraph (Fin n), BipartiteDD.IsBipartiteDegDiam G Δ D`), with the staged method:

| theorem | n | Δ | D | file |
|---|---|---|---|---|
| nb_11_4_v2 | 1782 | 11 | 4 | records/bipartite_dd/d11D4/1782-gq4x-as_w2_q9_n1782.json |
| nb_13_4_v2 | 3146 | 13 | 4 | records/bipartite_dd/d13D4/3146-gq4x-as_w2_q11_n3146.json |
| nb_15_4_v2 | 5070 | 15 | 4 | records/bipartite_dd/d15D4/5070-gq4x-as_w2_q13_n5070.json |
| nb_16_4_v2 | 5440 | 16 | 4 | records/bipartite_dd/d16D4/5440-gq4-cover2_q13_n5440.json |

   Order: 1782, 3146 first (commit + push), then 5070, then 5440. If a 5000-vertex graph needs more memory or time per stage, split stages further (by start-vertex chunks within a radius), keeping every stage kernel-checked. Only if a graph is still infeasible after a fair try, prove it with native_decide under a separate name with suffix `_native`, and say so.
3. Keep existing theorems unchanged; keep sanity tests passing. Add the new theorems to `lean/Axioms.lean`, regenerate `lean/Axioms.out.txt` with `lake env lean Axioms.lean`, commit with a message starting `milestone:`, push.

## Rules
No `sorry`, `admit`, new `axiom`, or checking-weakening options; do not change IsBipartiteDegDiam or check_sound. Do not touch lean/BipartiteDD/GQ4/, GQST/, Plus2/ or ASq/.

## Final reply
What builds, total build time, per-theorem method and time, `#print axioms` lines for the new theorems, last commit hash.
