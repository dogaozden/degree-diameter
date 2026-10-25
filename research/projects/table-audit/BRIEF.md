# Audit the 2013 table

Project `table-audit` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Rebuild every entry of the published bipartite table (research/frontier/TABLE.md, heuristic.py `TABLE`) we can:
find who holds each value and the construction (reading papers and the Combinatorics Wiki on the web is fine;
contacting people is not), rebuild the graph, check it with apsp.c or the big checkers, and flag any entry that does
not check out or has no traceable construction. Deliverables in research/projects/table-audit/: one row per cell
(value, holder, source, rebuilt yes/no, check result, notes).

## Rules
- You are a Haiku worker (Doğa: Haiku first; Opus only where Haiku would fail). Read HANDOFF.md in this folder first if
  it exists (an earlier session started this) and continue from it. Small steps, each checked before the next.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; keep HANDOFF.md current so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c; Lean has no sorry, admit or
  native_decide (standard axioms); a new checker must agree with apsp.c on test graphs, including broken ones.
- Do not edit records, README or RESULTS.md. Never contact anyone or post anything outside this repo. Write plainly.
