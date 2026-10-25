# Finish the hexagon story at diameter 7

Project `hexagon-family` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

All our (7,7)..(16,7) records come from the generalized hexagon H(q): three copies (X(M)) or multi-level covers,
with a set R of pairwise-opposite points freed and hub vertices added (research/d13D7/, research/d10D7/,
research/coordinator_check/check_2026-10-24_*.txt, research/frontier/sols/d*D7_hex*). Every extra point of R adds
vertices. Goals: (1) find the largest pairwise-opposite (or whatever the construction really needs) point sets for
q = 7, 8, 9, 11, 13, 16 by large clique/SAT/orbit searches, and record each improvement as a graph; (2) write the
general construction and its diameter-7 proof for every q as a clean theorem (paper-style, research/projects/
hexagon-family/THEOREM.md), and formalise it in Lean as far as possible; (3) say what bound on |R| holds.

## Rules (all projects)
- You are an Opus lead (xhigh effort). Use the haiku-squad skill (.claude/skills/haiku-squad/SKILL.md): 8 Haiku
  subagents on separate strategies whenever you are stuck or want many tries at once; verify the best yourself.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; leave a HANDOFF.md in your folder so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c (or apsp_orb.c / the big checkers);
  proofs are Lean with no sorry, admit or native_decide (standard axioms), or a written proof plus a machine check.
- Do not edit records, README or RESULTS.md: the coordinator re-checks and records. Never contact anyone or post
  anything outside this repo. Write plainly.
