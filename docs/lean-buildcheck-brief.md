# Lean brief: full build check of master after the Oct 20 merges

Several Lean branches were merged into master on 2026-10-20 without a combined build (Doubling, Regular, Hexagon,
HexagonD incl. Identity, Plus2Zero, Records9592; lean/BipartiteDD.lean now imports all of them).
1. `lake exe cache get`, then `scripts/guarded.sh 3 lake build` of the whole library (lean/). Build heavy record modules
   one at a time if memory is tight (they need ~12 GB each).
2. If anything fails (name clashes between HexagonD and HexagonD.Identity, import cycles, changed APIs), fix it with the
   smallest change that keeps every theorem statement unchanged. No `sorry`/`admit`/`axiom`/`native_decide`.
3. Regenerate every Axioms.out.txt (lean/Axioms.out.txt, lean/RegularAxioms.out.txt, and each folder's Axioms.out.txt)
   and confirm only propext, Classical.choice, Quot.sound (or subsets).
4. Write lean/CHECK.txt: date, toolchain, Mathlib commit, build result, the list of axioms files with line counts.
Rules: `scripts/stop_check.sh` first; 3-hour limit. Branch `lean-buildcheck` from origin/master. Report the result.
