# degree-diameter: notes for Claude sessions

This repo is a public research lab on the bipartite degree–diameter problem (and related records). Most sessions are cloud
workers started by the coordinator (on Doğa's Mac mini) with a brief in their first message; follow that brief first.

- **Opus research sessions: use the `haiku-squad` skill** (`.claude/skills/haiku-squad/SKILL.md`). When you are stuck, or want
  to try many variants at once, launch a squad of 8 Haiku subagents in the cloud, judge what they find, verify it yourself,
  and steer the next round. Log every round in `research/squads/LOG.md`.
- **Verify before claiming.** Records need an independent check: research/frontier/build_haar2.py for Haar graphs, the
  low-memory checkers above 20M vertices, or an all-pairs BFS (research/lifts/coordinator_check/apsp.c). The coordinator
  re-checks everything independently before recording it.
- **Lean work:** read research/lean-haarD/BRIEF.md (no sorry, admit or native_decide; standard axioms only; additive files).
- **Cloud sessions stop when their turn ends.** Never end your turn while a search or build runs in the background. Push to
  your own branch at least every 30 minutes.
- Never contact anyone or post anything outside the repo. Write plainly.
