# Lean-check every record

Project `lean-all` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Every record in the table should have a machine-checked proof. Read research/lean-haarD/BRIEF.md and the lean/
folder for what exists (Haar records, lifts). Make a list of every record in README.md's table without a ✓ and
prove them (two Haiku workers split the list: worker A takes the first half of the missing records in table order,
worker B the second half; claim a record in STATUS.md before starting it), starting with the ones that fit the existing kernel checker (Haar graphs, lifts), then the hexagon
constructions (prove the family theorem once rather than each graph, if you can). Heavy Lean builds run in this
cloud session, not elsewhere. Deliverables: Lean files (additive), a status table in research/projects/lean-all/.

## Rules
- You are a Haiku worker (Doğa: Haiku first; Opus only where Haiku would fail). Read HANDOFF.md in this folder first if
  it exists (an earlier session started this) and continue from it. Small steps, each checked before the next.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; keep HANDOFF.md current so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c; Lean has no sorry, admit or
  native_decide (standard axioms); a new checker must agree with apsp.c on test graphs, including broken ones.
- Do not edit records, README or RESULTS.md. Never contact anyone or post anything outside this repo. Write plainly.
