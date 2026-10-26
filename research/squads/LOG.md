# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, own-small, round 1 (goal: (3,10) > 800; also (3,9), (3,7), (4,8), (4,9))

Session session_01TFYrqhzV4cEhot1ZWNt8vK, branch claude/own-small-cells-dkwo42. 16 Haiku cards (model haiku, effort
high), 17:05-17:50 UTC, folder research/squads/own-small/r1/ (HEADER.md, cards.md, scoreboard.jsonl). CPU gate
tools/slot.sh with 3 slots on a 4-core machine (remote isolation runs on the same machine, so it adds no CPU).
Director before the round: cubic VT census (all graphs on 290..1,280 vertices) and Foster census (edge-transitive, up to
10,000) give nothing at D = 8, 9, 10; 2+2 lifts over every group of order 200..250 fail at D = 10 (exhaustive).
Cards (best n / far pairs, (3,10) unless noted):
- a1 symmetry-breaking repair of the 880 near miss (requot to index 2..10, re-anneal): no move (880 / 220).
- a2 all groups of order 136 with 3+3 bases + repair of 816: not reported in the round. a3 delete-and-rematch: no move (816 / 136).
- b1 Tutte 12-cage covers (Z7, order 8): 882 / 12,201. b2 small edge-transitive bases x all groups: not reported in time.
  b3 mid-size edge-transitive bases x small groups: not reported in time.
- c1 3+3 x 73 non-abelian groups of order 134..170 (0.8 s screens): cost 8 at 840. c2 4+4 x 159 groups of order 101..125:
  864 / 432. **c3 5+5 joint base+voltage annealing (salift, D = 10) over SmallGroup(81,4): 810, cost 2 after one 95 s run.**
- w1 semi-edge 2-vertex bases with parity: 812 / 1,015. w2 group filter + 7+7 over order 60: 840 / 1,320.
- e1 (3,9) 3+3/4+4 all groups: not reported in time. e2 (3,9) covers of edge-transitive bases: 544 / 1,088.
- h1 (3,7) delete-and-rematch from the 180 near misses: not reported in time. f1 (4,8) 2+2 quartic over orders 547..550:
  2,196 / 4,941. w3 (4,9) wildcard: not reported in time.
Kept: c3's idea. The director re-ran it over all 15 groups of order 81 (45-120 s each, salift_s): **two valid (3,10) graphs
on 810 vertices** (SmallGroup(81,12) = C3 x He3 and SmallGroup(81,9)), checked with score48 and apsp.c, rebuilt from
explicit C3 x He3 coordinates (research/squads/own-small/records/). Five more groups reached cost 2-4. 6+6 over order 81
(n = 972) stays at cost 66+. Lesson: the gate queue (3 slots for 16 cards plus GAP exports outside it) starved several
cards; round 2 uses pre-exported groups, one gated job per card and 4 slots.
Next: round 2 spreads joint annealing over (p, N) slots with n = 812..1,008, plus (3,9) at D = 9 and a degree-4 version.
