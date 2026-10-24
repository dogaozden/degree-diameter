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

## 2026-10-24, thm-chartlift round 3 session (session_01DZd593abAfRP1TbgB8wqYh), squad r2-chartlift (22:10–23:10 UTC)

Lead going in (Opus, solo, ~60 min): resumed the cut-off session; found that charts covering BOTH diagonals free the
controller from 4-cycles, so Haar graphs of metacyclic groups work: (15,5) 25,272 (Z26 x|3 Z6, m=156) and, after
proving that (4,3) charts can cover both diagonals (star-collineation reduction, exhaustive search), (12,5) 10,368
(Z16 x|3 Z4, m=64). Both rebuilt and checked (apsp + bfs_all). Cards (folders research/squads/r2-chartlift/c1..c8;
brief COMMON.md):
1. (15,5) Haar push, metacyclic orders 157-176 with the 112 chart.
2. (15,5) better (5,3) charts (fewer than 112 singular, both diagonals, pencils).
3. (15,5) non-Haar: 2+2 and 3+3 bases at m = 158-176.
4. (10,5) Haar sweep at orders 126-150 with the 230 (5,2) chart (table needs m >= 126).
5. (10,5) better (5,2) charts.
6. (8,5) Haar and small bases at m >= 65 with the 48 (4,2) chart.
7. (14,5) seven letters over F2: chart + Haar at m >= 462.
8. (12,5) six letters over F2: chart + Haar at m >= 274.

Outcomes:
1. no gain: best cost 4 at m=160 (meta:20:8:3 and 20:8:13, three seeds each, flat), 6 at 168; 25 of 37 sweep groups not run.
2. no gain for the record: best chart 106 singular (old annealer); note: two parallel b-vectors force >= 64 singular.
3. no gain: best cost 6 at m=160 (2+2 over meta:20:4:9/11); 3+3 far worse.
4. **record: (10,5) 4,032** (Haar Z14 x|9 Z9, m=126), rebuilt and checked here (apsp VALID, bfs_all max_ecc 5); also
   m=112, 120 valid; other order-126 groups cost 1-17.
5. (5,2) chart with 216 singular (from 230); second m=126 controller (Z21 x|4 Z6, same 4,032, apsp VALID); m=128 cost 1.
6. no gain: exhaustive Haar over all 128 groups of order 60-81 fails with the 48 chart (min cost 4); 2+2 best cost 2 at
   m=66. (The lead then proved 48 is the minimum for (4,2) charts covering both diagonals, r3/dpmin.)
7. no gain for the record: (7,2) chart 1,314/3,024 singular; Haar m=300 valid (9,600), cost 44 at m=462.
8. no gain: (6,2) chart 602/1,500 singular; Haar cost 2 at m=200, 31 at m=280.

Kept: Haar graphs of metacyclic groups Z_M x| Z_N with N = 4..9 for diagonal-covering charts; chart quality is the
bottleneck at q=2 for k >= 6. Next: round r3-chartlift (multi-orbit bases for (12,5), the 92 chart for (15,5), (10,5)
past 126, star-move charts for (7,2), non-metacyclic groups).

## 2026-10-24, thm-chartlift round 3 session, squad r3-chartlift (23:05–00:00 UTC)

Lead going in: (4,3) diagonal charts classified (16 singular, 348 labelled singular sets), Haar controllers shown to stop at m=64 for (12,5) for 7 of the
24 chart classes (the other 17 scanned later), (5,3) charts down to 92 singular (star-move annealer), the central-involution obstruction
for Haar graphs. Cards (folders research/squads/r3-chartlift/c1..c8; brief COMMON.md):
1. (12,5) 2+2 bases over |G| = 33-40 with the (4,3) chart classes.
2. (12,5) 3+3 bases (incl. K3,3 + doubled matching) over |G| = 22-27.
3. (12,5) 4+4 bases (K4,4 Latin and others) over |G| = 17-20.
4. (15,5) Haar at orders 157-170 with the 92 chart.
5. (15,5) better (5,3) charts with the star-move annealer.
6. (10,5) push past m=126 (Haar 128-140, 2+2 bases, better (5,2) charts).
7. (14,5) better (7,2) charts, then Haar at m >= 462.
8. Wildcard: Haar graphs of direct products (non-metacyclic groups).

Outcomes (filled in as cards report):
2. **(12,5) 11,664** (m=72, K3,3 + doubled matching over Z3 x|2 Z8, class-1 chart), rebuilt and checked here; also
   m=66, 69 valid; Z25 (m=75) cost 2, Z26 8, Z27 10. The lead then scored the Z25 voltages against all 348 labelled
   singular sets: set s170 gives cost 0 -> **(12,5) 12,150**, rebuilt and checked (apsp, bfs_all).
3. **(12,5) 11,664** again (m=72, K4,4 Latin over Z3 x Z6) and m=68 (Z17) valid; nothing at 76, 80.
5. (5,3) chart with 88 singular (same count as the lead's coordinate descent); m=160 still cost 2.
1. (12,5) m=72 valid (2+2 base k4r2_001 over Z6 x|5 Z6, class 1; apsp VALID per the card), m=68, 66 valid; best near
   miss above: m=80 cost 4 (base k4r2_000 over Z5 x|2 Z8) -> handed to the lead's 348-set alternation.
4. (15,5): order-168 near miss Z28 x|11 Z6 at cost 2 (92 chart) -> the lead re-optimised the chart for it (controller-
   aware coordinate descent): **(15,5) 27,216**, rebuilt and checked (apsp, bfs_all). Also 165 and 168 near misses.
7. no gain: (7,2) chart 1,262 of 3,024 singular (from 1,314); Haar m=462 cost 36, m=432 36, m=480 45.
8. no gain: direct products (SL(2,3) x Z3, A4 x Z6, S4 x Z7, SL(2,3) x Z7, ...) do no better than metacyclic groups:
   (12,5) m=72 cost 2 (SL(2,3) x Z3), (15,5) m=168 cost 4.
Lead, after the cards: c1's m=80 near miss (cost 4) -> r3/alt348.sh -> **(12,5) 12,960** (rebuilt, apsp + bfs_all).
Kept: the joint optimisation (controller fixed, chart re-optimised; at (4,3) by scoring all 348 singular sets). It
turned three near misses from the squad into records (12,150, 12,960, 27,216).
6. no gain: (10,5) best m=128 cost 1 (Haar Z16 x|3 Z8), cost 2 (Z32 x|9 Z4, Z16 x|5 Z8); 2+2 bases cost 4 at m=128.
