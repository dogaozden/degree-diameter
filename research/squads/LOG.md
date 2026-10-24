# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 18:55–19:30 UTC, cell-14-7 (Opus, cloud session), round 1 (16 cards, two squads of 8): (14,7)

Goal: beat (14,7) = 1,771,560 (Delorme–Gómez–Quisquater polygon cover: GH(11) + 2 matchings over Z5). Opus before the
round: built GH(q) (gh_build.c) and a lift annealer (glift.c); found that one copy past 2j+1 works at small q
(GH(2)+1 over Z4, 504, apsp VALID) but random matchings leave ~27,600 misses per source at q = 11 (Z6).
Brief: research/squads/d14D7-r1/BRIEF.md; cards research/squads/d14D7-r1/cards/; scoreboard scoreboard.jsonl.

Cards: c1 Weyl-distance building scan at D ≤ 7 · c2 literature · c3 GH(q) over GF(4), GF(8), GF(9) and the
GH(9)+4 / GH(8)+5 regime · c4 how many copies for GH(3)+2 · c5 targeted annealing for one matching over Z4 ·
c6 Singer-symmetric matchings · c7 route-chart lifts at D = 7 · c8 wildcard · c9 GH(11)+2 configurations over
order 6–8 · c10 GH(5)+2 over Z6 (→ (8,7)) · c11 GH(7)+2 over Z6 (→ (10,7)) · c12 counting bounds for extra copies ·
c13 Haar baseline at (14,7) · c14 polygon cover + extra vertices · c15 GH(13) with rewired matchings · c16 wildcard.

Best per card (valid unless noted): c1 none (A2–A5 scanned, rest unscanned; fixed a pruning bug) · c2 no newer
bipartite D = 7 record; general (14,7) = 6,200,460 (Gómez–Fiol–Serra compound on GH(11)) · c3 GH(4), GH(8), GH(9)
built; random misses/source GH(9)+4/Z14 6,031, GH(8)+5/Z24 5,290 (not valid) · c4 GH(3)+2 over Z6 = 4,368 (apsp
VALID), Z7 not reached · c9 best 8,006 misses/source (Z6, random polygon voltages; not valid) · c10 GH(5)+2/Z6 full
cost 253,776, annealing −4 % (not valid) · c12 counting does not exclude (11,2,m=6..8) · c14 **+60 vertices on
GH(3)+2 over Z5** (3,640 → 3,700, apsp VALID; delete base edges, attach new vertices; a Z5-symmetric unit of +2 is
valid alone) · c16 LPS Ramanujan Cayley graphs: (14,7) only 205,320 · c8 GQ lifts without matchings fail (girth) ·
c5, c6, c7, c11, c13, c15: no report before the round was closed or no valid improvement (see their folders).

Kept: c14's unit. Opus turned it into a construction with a proof: delete one matching edge (p, l) in all copies and
add z ~ {(p,c)}, z' ~ {(l,c)}; only the routes from (p,c) to points opposite p and from (l,c+h) to lines opposite l
break, and they are repaired exactly by prescribing sigma_t on the points at distance 4 from p (the 14,641 lines at
distance 4 from a line M through p, not projecting onto p, partition the opposite points). **Result: (14,7) 1,771,562
(one unit; ucheck12 over all sources VALID; apsp running).** The same construction beats every DGQ value: D = 5
(10,5)…(15,5) all apsp VALID, and (7,7) 23,438 apsp VALID (research/cell147/units/README.md).
Squad assessment: the round produced the decisive idea (c14). The other cards mostly confirmed negatives
(extra copies at large q, random-like constructions, buildings, LPS) — useful for the cell notes.
