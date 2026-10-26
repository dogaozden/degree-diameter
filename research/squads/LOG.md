# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, hunt-d5 (Opus, cloud session_01G9FwCXeEt4mUvAMjcr9j11), round 1: (5,5), (7,5), (9,5)

Goal: bipartite diameter-5 graphs above our 354 / 1,152 / 2,662, searched in the windows Haar order 193–224 / 606–630 /
1,378–1,410 (and lifts of the same sizes). 16 Haiku cards (model haiku, effort high), 13:40–14:20 UTC, 4 shared cores.
Director tools first (research/squads/hunt-d5/tools): GAP SmallGroups tables, haar5 (D = 5 Haar annealer with
automorphism orbits), flift/lift from b48. Cards, scoreboard and work folders: research/squads/hunt-d5/r1/.

Cards: a1 (5,5) Haar 193–207 · a2 (5,5) Haar 208–224 · a3 (5,5) 3+3 lifts over 65–75 · a4 (5,5) 2+2 / 4+4 lifts ·
a5 (5,5) wildcard (6+6 lifts) · b1 (7,5) Haar 606–622 · b2 (7,5) Haar 608–630 · b3 (7,5) 5+5 / 6+6 lifts · b4 (7,5)
2+2 / 3+3 / 4+4 lifts · b5 (7,5) wildcard (products, 7+7, 11+11) · c1 (9,5) Haar "3 3 0" orbits 1378–1400 · c2 (9,5)
other orbit shapes · c3 cubic route-chart controllers · c4 (9,5) small-base lifts · c5 (9,5) wildcard (GQ + matchings)
· x1 global wildcard (bi-coset graphs, lifts of PG(2,4)).

Best per card (cost = uncovered pairs; 0 would be a graph): a1 8 (C41⋊C5, 204/6, 200/40; 3 s screens) · a2 15
(210/2) · a3 30 (Z65; 1 s runs) · a4 16 (100/7, 104/3) · a5 82 · **b1 4 (SmallGroup(615,1))** · b2 12 (624/134) · b3 79
· b4 30 (meta 61:5:9, 19:16:18) · b5 13 (S₄ × Z₂₇) · c1 none (no usable automorphism at 1392) · c2 8 (C197⋊C7,
1379) · c3 controllers m = 16 (m = 17: 6) · c4 16 (C53⋊C13, 2+2 base, n = 2,756) · c5 5,234 · x1 834.
No valid graph in the windows.

Director meanwhile: a 3-letter route chart over F₃⁴ with every non-backtracking pattern nonsingular and both pencil
conditions (also over F₄⁴), so any cubic bipartite controller with same-side distance ≤ 4 and a 4-cycle at every
vertex lifts to a (9,5) graph on 162m vertices (m = 12, 16 checked all-pairs). Controllers stop at m = 16 (three
annealers stall at 6 for m = 17): 2,592 < 2,662, so not a record. Non-abelian coset fibres (order 81): worse.

Kept for round 2: metacyclic-type groups (615/1, C197⋊C7, C41⋊C5), K_{Δ,Δ} lifts (new), the m = 17 controller,
q = 2 route charts for (6,5) (a cell we do not hold), exhaustive orbit certificates (new haar5 exho mode).
