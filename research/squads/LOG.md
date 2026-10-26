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

## 2026-10-26, own-small, round 2 (goal: (3,10) > 810 by joint annealing; (3,9); quartic cells)

17 Haiku cards planned, 15 launched 17:50-18:12 UTC (research/squads/own-small/r2/). Each card got one (p, N) slot for
salift_s2 (joint base+voltage annealing, START restarts) and one gated job of <= 900 s; 4 gate slots, groups
pre-exported. What went wrong: cards started their gated job as a background tool call, and the 30-minute limit on
background calls killed every job still waiting in the gate queue around 18:20-18:35, so only about 8 of the 15 jobs
ran (k9 and q1 never started). Lesson: a card's wait in the queue counts against its own background time limit; for
heavy rounds the director should run the compute queue directly and use cards for ideas.
Best state per card (salift cost; far pairs = cost * N / 2), (3,10) unless noted:
- k1 4+4 N=102..110: cost 8 at 864. k2 5+5 N=82..86: cost 4 at 820. k3 5+5 N=87..92: 20 at 880. k4 6+6 N=68..72: 4 at 816,
  6 at 864. k5 6+6 N=73..80: 26 at 912. k6 7+7 N=58..63: 6 at 812. k7 8+8 N=51..56: 20 at 832. k8 9+9 N=45..50: 40 at 864.
  k10 prime-power groups: 60 at 896 (order 64), 66 at 1,000 (order 125). k11 n = 960..1,008: 78 at 960. k9: no job ran.
- m1 (3,9) 5+5/6+6 at D = 9: cost 8 at 510. m2 (3,9) 8+8 over order 32: 12 at 512.
- q1 (4,8): wrote a degree-4 joint annealer (salift4.c, validated by the director against score48) but its job never ran.
- w4 wildcard: parallel tempering inside one process was not better than plain salift at equal CPU (810: 8/14/8 vs 4/12/8).
Director during the round: polish (exact search over all 1- and 2-voltage changes and endpoint swaps) shows the best
states at 812 (6), 816 (4), 820 (4) and (3,11) 1,296 (2) are exact local minima; inserting 2 vertices into the 810 graph
(all 36,300 two-edge insertions) fails.
No valid graph above 810. Kept: (3,10) cost rises with n (cost 4 at 816/820, 20+ at 880+); short independent runs beat
long pushes. Next: the director runs quartic joint annealing ((4,8): cost 64+ at n = 2,200 with p = 4..6, far) and
Haar scans, (4,9) over the 5-groups of order 625 (n = 5,000), and (3,11) above the census value 1,250.

## 2026-10-26, own-small, round 3 (goals: (3,11) and (3,12) new cells, (3,10) > 810, (3,9) > 506)

16 Haiku cards, 19:35-20:50 UTC (research/squads/own-small/r3/: HEADER.md, cards.md, scoreboard.jsonl). New setup after
round 2's lost jobs: cards ran no heavy programs themselves; they appended task lines to the director's queue
(tools/dispatch.sh, 4 workers, round-robin over cards, at most 14 tasks of <= 90 s per card) and evolved from the result
lines; cost-0 states were converted and checked with score48 automatically. Throughput was the limit: about 210 tasks
ran in 75 minutes, cards got 6-10 results each, and most cards ended with tasks still queued.
Cards (best valid n / best near state; salift cost):
- (3,11), D = 11: x1 6+6 N=106..112: 1,284 cost 2 and 1,272 cost 2 (after polish). x2 7+7 N=91..96: 1,274 cost 6.
  x3 8+8 N=79..84: 1,264 cost 4. x4 5+5 N=127..135: 1,290 cost 4. x5 9+9/10+10: 1,314 cost 6.
  **x6 4+4 N=158..165: VALID 1,320** (SmallGroup(165,1) = C3 x (Z11:Z5)).
- (3,12), D = 12: y1 6+6: 2,352 cost 28. y2 7+7: 2,310 cost 28. y3 8+8: 2,320 cost 30. y4 5+5: 2,310 cost 86. y5 9+9/10+10:
  2,320 cost 40.
- (3,10), D = 10: z1 5+5 N=82..86: 820 cost 6. z2 6+6/7+7: 816 cost 8. z3 4+4 N=102..104: 816 cost 6.
- (3,9), D = 9: v1 5+5/6+6: 510 cost 8. v2 larger bases: 512 cost 12.
Director, from x6's result (4+4 bases work best at D = 11): 4+4 tasks over orders 168..200 gave **VALID 1,344**
(SmallGroup(168,1) = Z7 x|_5 Z24), and cost 4 at 1,360 and 1,368; the same idea at D = 12 (orders 289..300) gave cost 4
at n = 2,352 (order 294) and 8 at 2,400, far better than the cards' p = 5..10 slots (cost 24+). Records rebuilt from
explicit group coordinates and checked with apsp.c (research/squads/own-small/records/).
Kept: 4+4 bases are the strongest at D = 11-12, 5+5 at D = 10. A second, FIFO queue (tools/dispatch2.sh) then ran
only the promising pending tasks (4+4 at D = 11/12, (3,10) n = 816 seeds).

## 2026-10-26, own-small, director after round 3 (no Haikus)

FIFO queue (tools/dispatch2.sh) on the promising pending tasks, then focused runs. 4+4 joint annealing at D = 12 reached
cost 2 at n = 2,368 (Z37 x|_6 Z8 = SmallGroup(296,3)); the exact two-move search tools/polish.c (all single and pairs of
voltage changes, endpoint swaps) then found a cost-0 state: **(3,12) new cell, 2,368 vertices** (census best 2,304,
lab 1,320), checked with score48 and apsp.c and rebuilt from explicit metacyclic coordinates. Polish found nothing from
the cost-4 states at (3,11) 1,360 / 1,368 and (3,12) 2,352 (exact local minima). Lesson: annealing plus an exact
two-move polish can finish what annealing alone stalls on: of the four cost-2 states polished ((3,11) 1,272, 1,284,
1,296 and (3,12) 2,368) one was two moves from a valid graph; none of the cost-4 states was.
