# Lean-check every record

Project `lean-all` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Every record in the table should have a machine-checked proof. Read research/lean-haarD/BRIEF.md and the lean/
folder for what exists (Haar records, lifts). Make a list of every record in README.md's table without a ✓ and
prove them, starting with the ones that fit the existing kernel checker (Haar graphs, lifts), then the hexagon
constructions (prove the family theorem once rather than each graph, if you can). Heavy Lean builds run in this
cloud session, not elsewhere. Deliverables: Lean files (additive), a status table in research/projects/lean-all/.

## Rules (all projects)
- You are an Opus lead (xhigh effort). Use the haiku-squad skill (.claude/skills/haiku-squad/SKILL.md): 8 Haiku
  subagents on separate strategies whenever you are stuck or want many tries at once; verify the best yourself.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; leave a HANDOFF.md in your folder so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c (or apsp_orb.c / the big checkers);
  proofs are Lean with no sorry, admit or native_decide (standard axioms), or a written proof plus a machine check.
- Do not edit records, README or RESULTS.md: the coordinator re-checks and records. Never contact anyone or post
  anything outside this repo. Write plainly.
