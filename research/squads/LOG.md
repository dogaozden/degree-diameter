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

## 2026-10-25 07:28–07:54 UTC, table-audit lead (Opus), round table-audit-r2

Goal: (3,10) = 800 (Delorme–Gómez–Quisquater, unpublished; C720.3 has 720), a cubic bipartite graph of diameter 10
with at least 800 vertices, scored by apsp.c. Round r1 had reached 22 and 38 unreached pairs.

Cards (best per card, unreached ordered pairs unless noted):
- c1 symmetric SA (round r1's c6 code) over 10 (b, c) splits: best (10, 80), cost 8 over orbit representatives
  (640 ordered pairs); splits with b = 4 or b ≥ 16 were far worse.
- c2 voltage lifts of Desargues, Möbius–Kantor, Q3 over non-cyclic groups: 40 (Q3 over Z20 × Z5).
- c3 Haar graphs over non-metacyclic groups of order 400–408: 22 (SL(2,3) × Z17, 816 vertices), F20 × F20 26.
- c4 exhaustive Haar H(G, {e, a, b}) over 172 groups of order 400 (card's own group tables, not re-checked by the
  lead): no diameter-10 graph, best 10.
- c5 lifts of cages (Heawood over Z58 / D29, W(2) over order-27 groups, H(2) over Z7): 42.
- c6 joint SA over base multigraph and voltages: 40 (b = 20, Z40); worse than r1's 22.
- c7 2-switch SA from Haar starts: VALID only at n = 500.
- c8 growing C720.3 by bipartite gadgets plus repair: 961.

Kept: nothing new; (3,10) = 800 stays unreproduced and untraced. The closest approaches are symmetric (c1, c3), so
a next round would run c1's (10, 80) and (12, 67) splits for minutes rather than seconds, and Haar graphs over the
order-400 groups c4 did not cover. Files: research/squads/table-audit-r2/.
Follow-up (lead, same morning): one 41-min run of c1's best setting (r1 c6 sym_anneal, b = 10, c = 80, T0 = 6,
seed 11) reached cost 0, so (3,10) = 800 is now reproduced (research/projects/table-audit/graphs/
d3D10_n800_symZ80_b10.edges.txt, apsp.c VALID). Seven runs at 810 and one at 820 stopped at cost 2–6.
