# Lean merge brief (autopilot, cloud)

Goal: one branch, `lean-all`, that holds every Lean proof from the Oct 17–19 runs, builds cleanly, and has a fresh
lean/Axioms.out.txt.

## Autopilot rules (always)
- Before each step below, run `scripts/stop_check.sh`. If it prints STOP: commit what you have, push, and end.
- Run every long command through `scripts/guarded.sh HOURS ...` (it adds a time limit and the stop check).
  Total time limit for this whole job: 4 hours.

## Steps
1. Start `lean-all` from `origin/research-diam4`.
2. For each remote branch below, merge it unless it is already an ancestor (`git merge-base --is-ancestor`):
   claude/lean-haar-record-iosw8s, claude/lean-d5-record-theorems-th6ybb, claude/lean-records3-graphs-6719pq,
   claude/lean-final-singer-c-r9xece, claude/lean-asq-bound-lk0k7y, lean-gqst, lean-records2,
   then any other branch whose name contains `lean` that is not yet contained.
   Resolve conflicts by keeping both sides' theorems (Axioms.lean and BipartiteDD.lean imports are the usual ones).
   Never delete a theorem, never add `sorry`, `admit`, `axiom` or `native_decide`.
3. In lean/: `scripts/guarded.sh 3 lake build` (get the Mathlib cache first with `lake exe cache get`).
4. Make lean/Axioms.lean print the axioms of every top-level result (all nb_* theorems, ASq.bound, the GQ4/GQST copy
   theorems, SingerC.propC_subspace, the Haar lemma), run it into lean/Axioms.out.txt, and check that every line
   lists only [propext, Classical.choice, Quot.sound].
5. `grep -rnE '\bsorry\b|\badmit\b|^\s*axiom |native_decide' lean/BipartiteDD` must print nothing.
6. Write lean/MERGE.md: branches merged (with commit hashes), branches skipped and why, build time, the theorem list
   with each statement's first line, and the grep result.
7. Commit and push to `lean-all`. Do not touch master; the main session merges it.
