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

## Oct 25, cell-12-5 round 2 (same session), ~15:12–15:50 UTC

Goal: raise (12,5) above 11,178 (m = 69, found by Opus at 15:08 with a backtrack-complete chart held fixed).
Cards (research/squads/d12D5-r2/CARDS.md): c1 K33m/Z_24 fixed charts; c2 K33m/Z_25..27 (fake ceiling + fixed
charts); c3 K33m over non-cyclic groups of order 24–27; c4 single-orbit (Haar) controllers, orders 70–84; c5 k = 2
bases, orders 35–40; c6 other k = 3 bases; c7 k = 4 bases, orders 18–21; c8 chart diversity.
While the cards ran, Opus added chart VARIANTS (same leg triangles, other collineations) and a diagonal-preserving
chart move (VARLIST) and got m = 72 (11,664) and m = 75 (12,150), both apsp VALID, within minutes. That superseded the
fixed-chart cards; Opus stopped c1 and c2 early and told c8 to switch to variant pools.
Card results (free-diagonal fake ceilings unless said otherwise):
- c2: K33m fake ceiling Z_25 0, Z_26 4, Z_27 0 (m = 81); fixed chart real cost 4 (m = 75), 10 (m = 81).
- c3: non-cyclic order 24 reach fake 0 too, but Z_5×Z_5 4 vs Z_25 0, order 27 non-cyclic 8–10 vs Z_27 0.
- c4: Haar k = 1 closed: exhaustive minimum 2 over 163 groups of order 70–84 (central involutions stay uncovered);
  Opus's exh_k1r.c over 120 chart variants agrees.
- c5: k = 2 bases fake 4–16 at m = 70–80 (one 10 s zero at m = 76). c6: k3_000 fake 0 at 72, 75 but 8 at 81
  (Opus: 12 at 87). c7: k = 4 below K33m.
Kept: K33m over cyclic groups of odd order is the best family; its fake ceiling is m = 81 (Z_28: 4, Z_29: 12).
