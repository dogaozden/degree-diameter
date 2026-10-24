# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:00 UTC, cell-10-8 session, goal: beat (10,8) table 1,176,480, round d10D8-r1

Cards (scoreboard research/squads/d10D8-r1/scoreboard.jsonl):
- c1 hexagon lift H(q) + 2 matchings, Z_r hexagon voltages × Z5 levels: c_max(2) = 45, c_max(3) ≥ 25 (formula 15, 20), APSP-verified. Score 25.
- c2 same, free voltages / Z_m levels: q=3 m=20 valid, q=3 m=30 and q=4 m=20 not. Score 0.
- c3 nonabelian voltage groups: q=4 best A4 (order 12); order 16 near misses. Score 12.
- c4 q=7 scaling probe of hexagon lifts (pending).
- c5 Haar group screen for k=3/k=5 in the window (pending).
- c6 annealer schedule on proxy psl 25 × Z73: nothing solved in 120 s (best 4–9); COOL=10 REHEAT=60 weakly best. Score: censored.
- c7 wildcard: PG(2,9) incidence graph lifted by Z4000: valid at (10,8) with 728,000 vertices (0.62 of the table).
- c8 hubs on the Z10 hexagon lift at q=3: +15 vertices, APSP-verified (7,295 vs 7,280); does not close the 3× gap at q=7.
Kept: nothing beats the cell. The small-q slack of the hexagon family (c1) does not transfer: at q = 7 a random-like
voltage assignment has ~3·10⁶ uncovered (source, target, sheet) triples against ~2·10⁵ free variables (cell notes §3).
Lesson: 8 Haiku cards with their own test runs slowed the 3 main haar_sym runs about 4× (memory contention), so the
next round has to be lighter. Next: 4th main run; duplicate-word analysis (ZOPT, research/d10D8/zopt/).
