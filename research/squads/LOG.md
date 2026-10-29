# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-29, job beyond-haar-d5 (Opus cloud session), goal (5,5) > 354 and (7,5) > 1,152 without Haar graphs

### Round bh5-r1 (18:55 UTC, 8 cards, research/squads/bh5-r1/)
Cards: c1 (7,5) 2+2 lifts, orders 290-300 · c2 (7,5) 3+3 lifts, orders 194-200 · c3 (7,5) 4+4..6+6 lifts, orders
97-150 · c4 (7,5) GQ lifts (W(4)+2 over order 7/8, W(5)+1 over order 4, W(3)+3 over 15/16) · c5 (5,5) small-base
lifts (2+2 over 89/90, 3+3 over 60, 4+4..6+6, W(2)+2) · c6 (5,5) surgery on 354/352 · c7 (7,5) surgery on 1152/1140 ·
c8 bi-coset graphs (wildcard).
Best per card (cost = uncovered pairs, 0 = valid): c2 28 at 1176 · c3 36 at 1176 · c5 6 at 360 (2+2 over
SmallGroup(90,5)), 8 at 356 (Z89) · c6 152 far pairs at 356 · c7 436 far pairs at 1154 · c8 8 at 366 (order 366,
|H| = 2; but |G| = 2 x odd makes it a Haar graph of the index-2 subgroup) · c1, c4: see below.
Kept: the (5,5) small-base near misses; bi-coset graphs with |G| divisible by 4. Dropped: surgery (rigid records),
bases with more than 8 vertices (worse, as the coupon-collector law predicts).
Opus alone meanwhile: exhaustive search of all Z89-lifts of the 2+2 base [[2,3],[3,2]] (exh/cyc22.c, 22 CPU-min):
no solution, so no 356-vertex graph of that form. Solutions exist up to Z80 at least (320 vertices).
