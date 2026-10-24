# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, thm-chartlift (session_01REQ3iLuejMcoGSA6K5AUbR), goal: route-chart lifts beyond (16,5) — round 1 (18:40–19:10 UTC)

Lead going in (Opus, solo, ~70 min): general toolkit for route-chart lifts (any k, F_q, D = 5; research/theorems/chartlift/),
the projective reformulation (singular pattern = two meeting tripod lines; pencil = planes on <b_i, b_j>), and the first
new record: **(12,5) 8,748** (k=4, q=3, K3,3+matching over Z18; apsp + bfs_all VALID). Cubic controllers stop at m = 16
((9,5) 2,592 > table 2,496; (12,5) 8,192 < 8,200).

Cards (folders research/squads/r1-chartlift/c1..c8; shared brief COMMON.md):
1. (12,5) sweep of bases on <= 3+3 vertices x groups, m = 57-72.
2. (8,5) sweep of bases x groups (Haar allowed: the q=2 chart covers the diagonal), m >= 56.
3. (12,5) better (4,3) charts, then test at m = 57/60.
4. (8,5) better (4,2) charts and bigger bases (4+4, 5+5).
5. (16,5) a (4,4) chart with fewer than 8 singular patterns.
6. (15,5) and (10,5) with five letters.
7. Wildcard: joint annealing of chart and voltages for (12,5).
8. Wildcard: controllers that are not voltage lifts (colour-preserving switch annealing).

Outcomes:
1. no gain: m = 54 stays (K3,3+matching/Z18); m = 57-60 stall at cost 2 on five bases.
2. **better**: m = 56 (2+2 base over the dicyclic group of order 28), m = 60 (Z30), lifts 1,792 / 1,920, apsp VALID.
3. no gain: charts with 24 singular patterns (from 26) do not unblock m = 57 (cost 2 either way).
4. **best of the round for (8,5): m = 64**, K4,4 (Latin-square colouring) over Z2 x Z8 -> **2,048** (lab 1,764, table 1,710);
   Opus rebuilt it from the voltages with its own builder: apsp and bfs_all VALID.
5. no gain: the squad chart (8 singular) is locally optimal; 12,850 one/two-entry neighbours, symmetric ansatz, Singer scan.
6. **record: (15,5) m = 128**, 5-regular 2+2 base over the dicyclic group of order 64 -> **20,736** (table 20,496); Opus
   rebuilt and checked it (apsp, bfs_all VALID). (10,5): m = 112 (3,584) best, table needs m >= 126.
7. no gain: joint annealing reaches cost 2 at m = 57, 4 at m = 60.
8. no gain: general switch annealing far below voltage lifts (m = 44 for (8,5), 36 for (12,5)).

Kept: voltage lifts of small bases (K4,4 when the chart covers the diagonal, K3,3+matching when 4-cycles are needed),
non-abelian groups (dicyclic) at the frontier. Next: round 2 on all 26 4+4 base classes, exhaustive Z19 for (12,5),
(15,5) above m = 128, (10,5) to m >= 126, (16,5) above 66.
