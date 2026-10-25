# Checkers for the big cells at diameter 8 to 10

Project `bigcheck-dist` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Graphs in the big cells have hundreds of millions to billions of vertices; our checkers (apsp.c, apsp_orb.c,
research/frontier/haarcheck2.c, haarcheck_sl.c) cap out at tens of millions on one machine. Goals: (1) a verifier
that splits the BFS sources of a vertex-transitive or level-cover graph across many cloud sessions and merges
certified partial results (each part independently reproducible); (2) use symmetry (verified automorphisms, as in
apsp_orb.c) to cut the sources; (3) then search the big D = 8..10 cells for constructions (lifts with large groups,
hexagon/octagon-based covers) that these checkers make verifiable. Deliverables in research/projects/bigcheck-dist/.

## Rules
- You are a Haiku worker (Doğa: Haiku first; Opus only where Haiku would fail). Read HANDOFF.md in this folder first if
  it exists (an earlier session started this) and continue from it. Small steps, each checked before the next.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; keep HANDOFF.md current so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c; Lean has no sorry, admit or
  native_decide (standard axioms); a new checker must agree with apsp.c on test graphs, including broken ones.
- Do not edit records, README or RESULTS.md. Never contact anyone or post anything outside this repo. Write plainly.
