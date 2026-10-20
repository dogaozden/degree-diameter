# Lean brief: finish the (7,6) 9592 record (resume)

Start from branch `origin/claude/lean-9592-brief-oz6mj8` and read docs/lean-9592-status.md there: the graph, its level
modules, all 8 local chunks, G9592_local and stage s0 are built and kernel-checked. Left: `Stages.G9592_s1` … `_s5`
(~4 min and ~12 GB each — build ONE at a time), then `theorem nb_7_6 : ∃ G : SimpleGraph (Fin 9592),
BipartiteDD.IsBipartiteDegDiam G 7 6` (pattern of nb_16_4 in Records.lean, with a 6-way case split over stage0..stage5),
`#print axioms nb_7_6` in lean/Axioms.lean, regenerate Axioms.out.txt.

Rules: `scripts/stop_check.sh` before each step (STOP → commit, push, end); every build through
`scripts/guarded.sh HOURS ...`; total limit 4 hours; push after each stage. No `sorry`, `admit`, `axiom`,
`native_decide`; only propext, Classical.choice, Quot.sound. Push to branch `lean-9592b`. Report: files, build times,
the axioms line.
