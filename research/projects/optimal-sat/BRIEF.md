# Prove optimality in the smallest open cells

Project `optimal-sat` (Doğa, Oct 24 2026, 9:30 PM: "we have a lot of compute ... do all").

We find big graphs but have never shown that nothing bigger exists. Goal: prove N^b(Δ,D) exactly, or improve an
upper bound, in the smallest cells where the table value is not known optimal (research/frontier/TABLE.md and
heuristic.py `TABLE`; known optimal cells are marked in the coordinator's table data). Start with the cells nearest
the bipartite Moore bound in absolute terms (small Δ, D = 4..6). Methods: SAT/ILP encodings of "bipartite, max degree
Δ, diameter ≤ D, n vertices" with strong symmetry breaking (fix a BFS tree from one vertex, lex-leader constraints),
known structure (Moore-bound-minus-defect results: read the literature on bipartite graphs of defect 2, 4, 6),
and exhaustive generation where feasible. Deliverables in research/projects/optimal-sat/: encodings, solver logs,
proof certificates (DRAT for UNSAT where possible), and a plain summary of what is proved.

## Rules (all projects)
- You are an Opus lead (xhigh effort). Use the haiku-squad skill (.claude/skills/haiku-squad/SKILL.md): 8 Haiku
  subagents on separate strategies whenever you are stuck or want many tries at once; verify the best yourself.
- Work on your own branch claude/<project>-...; push at least every 30 minutes. Never end your turn while a job runs.
  Keep working until done or truly blocked; leave a HANDOFF.md in your folder so a fresh session can resume.
- Verify before claiming: graphs pass research/lifts/coordinator_check/apsp.c (or apsp_orb.c / the big checkers);
  proofs are Lean with no sorry, admit or native_decide (standard axioms), or a written proof plus a machine check.
- Do not edit records, README or RESULTS.md: the coordinator re-checks and records. Never contact anyone or post
  anything outside this repo. Write plainly.
