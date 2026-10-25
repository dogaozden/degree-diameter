# Checkers for the big cells at diameter 8 to 10

Project `bigcheck-dist` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

Graphs in the big cells have hundreds of millions to billions of vertices; our checkers (apsp.c, apsp_orb.c,
research/frontier/haarcheck2.c, haarcheck_sl.c) cap out at tens of millions on one machine. Goals: (1) a verifier
that splits the BFS sources of a vertex-transitive or level-cover graph across many cloud sessions and merges
certified partial results (each part independently reproducible); (2) use symmetry (verified automorphisms, as in
apsp_orb.c) to cut the sources; (3) then search the big D = 8..10 cells for constructions (lifts with large groups,
hexagon/octagon-based covers) that these checkers make verifiable. Deliverables in research/projects/bigcheck-dist/.

## Rules (all projects)
- You are an Opus lead (xhigh effort). Use the haiku-squad skill (.claude/skills/haiku-squad/SKILL.md): 8 Haiku
  subagents on separate strategies whenever you are stuck or want many tries at once; verify the best yourself.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; leave a HANDOFF.md in your folder so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c (or apsp_orb.c / the big checkers);
  proofs are Lean with no sorry, admit or native_decide (standard axioms), or a written proof plus a machine check.
- Do not edit records, README or RESULTS.md: the coordinator re-checks and records. Never contact anyone or post
  anything outside this repo. Write plainly.
