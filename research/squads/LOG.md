# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-25 05:05–05:22 UTC, table-audit lead (Opus), round table-audit-r1

Goal: reach the table order, with an apsp.c-valid graph, in five small cells whose holders' graphs are lost:
(3,8) 256, (3,10) 800 (Delorme–Gómez–Quisquater, unpublished), (6,5) 684, (4,8) 2,184, (4,9) 4,970 (Loz, data lost).
The lead ran plain metacyclic Haar graphs (haar_gen3) separately, so the cards excluded that.

Cards (best per card, apsp-checked by the lead where valid):
- c1 Bar-Yehuda–Etzion two-cycle graphs, SA over (s, F): reproduced BYE's 248 (3,8) and 672 (3,10); nothing new.
- c2 bipartite cubic Cayley graphs: nothing (best diameters 14 / 22).
- c3 voltage lifts of small cubic bases: **(3,8) 256 (Q3 over Z32) and 258 (K33 over Z43), both VALID**; (3,10) no.
- c4 lifts of small Δ = 4, 6 bases: nothing (K66 over Z57 gives 684 at D = 6, not 5).
- c5 Haar graphs over PSL(2,13), AGL(1,q) × Z_n: nothing (best cost 6–8).
- c6 cubic graphs with an imposed free Z_c, SA: **(3,8) 256 VALID** (b = 8, c = 32, 0.3 s); (3,10) best 36 unreached pairs.
- c7 reverse-engineering Hafner's Bond–Delorme files: 4.5 is a Cayley graph of its regular automorphism group
  (order 160); no new graph.
- c8 wildcard, growing Hafner's 660-vertex (6,5) graph to 684: nothing.

Kept: (3,8) = 256 is reproduced (two independent ways), so that table value is now rebuilt at its order. The lead's
metacyclic Haar run reached (6,5) = 684 (Z57 ⋊ Z6) and (5,5) = 336 (Z7 ⋊ Z24) in the same period, so (6,5) is covered
too. (3,10) = 800, (4,8) = 2,184 and (4,9) = 4,970 stay unreproduced. Next: longer lifts/orbit SA for (3,10);
metacyclic Haar for (4,8), (4,9) is still running in the lead's batch.
Files: research/squads/table-audit-r1/ (scoreboard.jsonl, per-card code).
