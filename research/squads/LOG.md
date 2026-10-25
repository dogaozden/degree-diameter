# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## Oct 25, cell-12-5 round 1 (resumed job, session_017fr6VuTNRS5rF6VytBNApG), ~14:16–15:00 UTC

Goal: raise (12,5) above 10,692 (found by Opus at 14:11 UTC just before the round, per-edge charts; the record before
that was 9,840). Cards (research/squads/d12D5-r1/CARDS.md):
c1 fake-chart controller ceiling, k = 3 bases × orders 24–27; c2 k = 4 bases × orders 17/18; c3 k = 2 bases × orders
34–38; c4 mlift_ejoint K33m over Z_23/Z_24 + apsp on near misses; c5 K33m over non-abelian order-24 groups; c6 faster
annealer; c7 wildcard (did k = 1 exhaustive and k = 5..16 tabu); c8 wildcard (exact lift-coverage checker).

Results (no card reached a VALID lift with m ≥ 67):
- c1: fake ceiling cost 0 only at m = 66; K33m/Z_24 cost 2 at m = 72; non-cyclic order-24 groups all worse.
- c2: k = 4 worse than k = 3 (best fake cost 4 at m = 68, 6 at m = 72). c5: non-abelian order 24 worse than Z_24.
- c4: K33m/Z_23 (m = 69) real cost 6–10; Z_24 cost 7–15; all near misses apsp INVALID.
- c6: incremental/tabu variant gives 3× more iterations, same final costs (6–10 at m = 69).
- c7: k = 1 exhaustive fake minimum 2 at m = 70 (Z_7×D_5) and 72 (Z_9⋊Z_8); k = 5..16 random bases no better.
- c8: exact checker (c8/exact_cover.c) agrees with the annealer's sufficient criterion on every near miss: the
  criterion is essentially tight, no exact-cost polish needed.
Kept: Opus read the m = 69 near misses: 6 of the 8 uncovered pairs are the six DIAGONAL orbits. Diagonals are the
bottleneck (with free diagonals the fake ceiling on K33m is m = 75). Next: make diagonals free through backtracking
closed walks (chart-only condition, EDGECHART.md), graded diagonal cost in mlift_ejoint2 (DGRAD=1).
