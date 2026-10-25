# Audit the 2013 table

Project `table-audit` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Rebuild every entry of the published bipartite table (research/frontier/TABLE.md, heuristic.py `TABLE`) we can:
find who holds each value and the construction (reading papers and the Combinatorics Wiki on the web is fine;
contacting people is not), rebuild the graph, check it with apsp.c or the big checkers, and flag any entry that does
not check out or has no traceable construction. Deliverables in research/projects/table-audit/: one row per cell
(value, holder, source, rebuilt yes/no, check result, notes).

## Rules (all projects)
- You are an Opus lead (xhigh effort). Use the haiku-squad skill (.claude/skills/haiku-squad/SKILL.md): 8 Haiku
  subagents on separate strategies whenever you are stuck or want many tries at once; verify the best yourself.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; leave a HANDOFF.md in your folder so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c (or apsp_orb.c / the big checkers);
  proofs are Lean with no sorry, admit or native_decide (standard axioms), or a written proof plus a machine check.
- Do not edit records, README or RESULTS.md: the coordinator re-checks and records. Never contact anyone or post
  anything outside this repo. Write plainly.
