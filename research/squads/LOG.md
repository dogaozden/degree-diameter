# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-27, job exact-3-7 (Opus, branch claude/bipartite-3-7-exact-zpbiyd): no squad round

Goal: exact results on the bipartite (3,7) cell (upper bounds with proofs, exhaustive searches). I ran no Haiku round.
The work was (a) proofs and (b) exhaustive enumerations whose cost is CPU on the 4 shared cores, which the
enumerations kept busy for hours; Haikus would have competed for the same cores, and the strategy space was narrow
(one exact method per family, validated by an independent second program). One Sonnet agent did the literature
search. Results: research/squads/cells/d3D7_exact.md. For the coordinator's comparison: "Opus alone" on this goal.
