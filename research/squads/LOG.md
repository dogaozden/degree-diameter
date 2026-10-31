# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-31 15:45-17:45 UTC, job handsoff-65 (hands-off Opus coordinator), goal (6,5) above 684, round 1
Cards (research/squads/handsoff-65/cards.md): c1 2+2 lifts orders 172-180 (tabu); c2 bigger-base lifts 3+3..8+8; c3 bi-coset
graphs of almost simple groups; c4 bi-coset |H|=|K|=2,3 at 722-766; c5 multi-orbit mcos types; c6 Haar + twisted matching;
c7 surgery on the 684 graph; c8 wildcard (generalized polygons; ended 16:18) -> c9 re-lift quotient bases of the 684 graph.
Best per card (n, far pairs): c1 704, 352 (lift cost 4, = prior); c2 696, 812 (cost 14, = prior); c3 720, 4320; c4 756, 2268
(cost 12); c5 732, 915 (1|3,3,3 on C2 x (C61:C3), cost 7); c6 720, 360 (Haar floor; no twist beats it); c7 686, 177 (684 graph
+ one vertex pair + guided SA; strict 2-opt minimum); c8 686, 9520 (GH(5,5) quotient). No graph above 684.
Kept: surgery (c13), 1|3,3,3 (c12), the c1 swap pattern (c11), the c4 sweep (c15); new: augmented quotient bases (c10),
re-coordinatised near misses (c14), wildcard (c16). Round 2 runs 17:45-19:45.

## 2026-10-31 17:45-19:45 UTC, job handsoff-65, round 2 (+ extras launched 18:20-19:30)
Cards: c10 augmented quotient bases (equivariant surgery); c11 swap-symmetric 2+2 lifts; c12 mixed-orbit mcos types;
c13 surgery continued; c14 near misses re-coordinatised as bigger-base lifts; c15 |H|=2 bi-coset rest of 722-766;
c16 wildcard (ended 18:57) -> c20 surgery downward; extras c17 tabu for coset graphs, c18 Haar + hub orbits
(1,k|1,k), c19 exhaustive Haar 802-840; c21 1,6|1,6 on orders 300-312.
Best per card (n, far pairs): c10 688, 312; c11 704, 2112 (cost 24); c12 762, 889 (1|3,3,3 floor cost 7 on 345-399);
c13 688, 320 / 690, 417 (686 floor 177 stays); c14 no descent (all near misses strict local minima); c15 750, 2250
(floor cost 12); c16 686, 1568; c17 728, 546 (3,3|3,3 cost 6); c18 686, 294 (1,6|1,6 on SmallGroup(294,11), mcos
cost 2, verified); c19 Haar orders 401-406 closed. No graph above 684.
Kept: the 1,6|1,6 hub family (new; c18 deep, c21/c25 other orders, c22/c23 other hub sizes, c26 non-cyclic hubs,
c24 free local search from it). Dropped: surgery upward, lifts, |H|=2 bi-coset, 1|3,3,3.

## 2026-10-31 19:30-21:05 UTC, job handsoff-65, round 3 (final)
Cards: c21 1,6|1,6 on orders 300-312; c22 hub type k=3; c23 hub type k=2; c24 free local search from the best graphs;
c25 1,6|1,6 on 318-342; c26 non-cyclic hub stabilisers; c27 finish Haar 416-420; c28 exact search of 1,6|1,6 on 294.
Best per card (n, far pairs): c21 no result (stalled); c22 688, 516 (1,3|1,3 on 258_2, cost 4); c23 720, 1080 (cost 15);
c24 686, 144 (best of the job, from c7's graph); c25 756, 2106 (cost 18); c26 686, 1029 (S3 hubs, cost 7); c27 Haar
orders 416, 418, 420 closed (with c19: Haar 802-840 closed); c28 cost-2 states of 294_11 are exact 2-change minima.
No graph above 684. Final split 37% Haiku / 63% Opus (session_usage). Report: research/squads/handsoff-65/REPORT.md.
