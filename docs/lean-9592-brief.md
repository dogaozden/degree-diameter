# Lean brief: the (7,6) record 9592 (kernel-checked graph) — Sonnet

Goal: `theorem nb_7_6 : ∃ G : SimpleGraph (Fin 9592), BipartiteDD.IsBipartiteDegDiam G 7 6`, for the graph
records/bipartite_dd/d7D6/9592-p4-hexagon-H5-whiskers.json, using the staged kernel-check machinery already on master
(lean/BipartiteDD/Staged.lean, StagedLocal.lean, lean/gen.py; see how nb_16_4 (5440 vertices, diameter 4) and
nb_15_4 (5070) were done — Stages/G5440_*.lean). Diameter 6 needs deeper stages than diameter 4; adapt gen.py.

## Autopilot rules (always)
- Before each step run `scripts/stop_check.sh`; if it prints STOP, commit, push, end.
- Long commands through `scripts/guarded.sh HOURS ...`; total limit 5 hours; build one heavy module at a time
  (parallel kernel checks ran out of memory before). Push progress every hour.

## Finish
`#print axioms nb_7_6` in lean/Axioms.lean, regenerate Axioms.out.txt. No `sorry`, `admit`, `axiom`, `native_decide`;
only propext, Classical.choice, Quot.sound. Branch `lean-9592`. Report: files, build time, axioms line, or exactly
where it got stuck.
