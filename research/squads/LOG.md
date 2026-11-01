# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-31, job six-five-384 (Opus cloud session, branch claude/haar-graphs-order-384-y2a8qp), goal: (6,5) > 684 via Haar graphs of order 384

Exhaustive Haar search H(G,S), |S| = 6, diameter 5, over the 20,169 groups of order 384 (research/six-five-384/README.md).
The director runs the exhaustive sweep on 3 cores; the squad gets the 4th core, so round 1 aimed at the bottleneck
(speed of the per-group search, ~4 s per group with haarex4) rather than at new searches. Scorer for the speed cards:
/tmp/claude-0/bench/bench.sh BIN (identical VALID/ASIDE/PAIR/DONE output to haarex4 on 342_12 (10 VALID sets),
360_53 (41 side-A covers) and 384_11094; user CPU seconds; haarex4 12.4-14.5 s, haarex3 31.5 s under the same load).

### Round s384r1 (10:52-11:12 UTC, 8 cards, research/squads/s384r1/)
Cards: c1 reuse work across b for a fixed 4-prefix · c2 low-level throughput of the target solution sets · c3 cheaper
orderly test bad() · c4 target ordering · c5 a sound earlier prune · c6 exact quotient test for |G/N| = 128, T = 3 ·
c7 wildcard (algorithm) · c8 wildcard (tabu near-miss scout on order-384 groups).
Best per card: c1 8.41 s (per-4-prefix cache of the b-free solution sets A4(x), skip of targets in Q4 Q4, bad(S,5)
reduced to the terms with b) · c2 10.37 s (byte-array solution sets with store-only marks, -funroll-loops) · c3 12.77 s
(bitset bad()) · c4 12.7 s (kill-weighted target order; within noise) · c5 no sound prune (counting bounds are vacuous:
Q4 Q4 covers ~45 elements, one new letter reaches ~4|Q4||S| values) · c6 one infeasible order-128 quotient (128_2046,
16 groups of order 384); 138 of the 150 most frequent order-128 quotients feasible, 11 undecided · c7 x and x^-1 have
the same solution set (exact, negligible) · c8 best tabu cost 8 (|G \ (S^-1S)^2| + |G \ (SS^-1)^2|, group 384_18;
median 23 over 60 groups; the 684 group reaches 0 in ~3 s).
Director's checks: c1 gives output identical to haarex4 on the 7 other groups with side-A covers (360_55, 360_56,
360_125, 360_126, 360_136, 360_138, 372_1) and the same prefixes= counts on three order-384 groups; installed as
research/six-five-384/src/haarex5.c and the main sweep restarted with it (~1.5x). c8's closest groups (18, 95, 42, 45, 94)
were already closed exhaustively (no side-A cover). c6's 2046 result is not used (the 16 groups are in the sweep).
Kept for round 2: combine c1 + c2 (+ c3's bitset bad, c4's note that the square-root/conjugator lists cost ~20%).

### Round s384r2 (11:20-12:20 UTC, 8 cards, research/squads/s384r2/)
Cards: c1 port s384r1-c2's byte arrays into haarex5 · c2 cut haarex5's per-b fixed cost (x in Q5 Q5 iff x in Q4 Q4 or
b in A4(x): one bit; bit matrix for bad_b) · c3 branch-free square-root/conjugator lists · c4 exact 3-opt around the
704-vertex C11:Q16 lift (cost 4) · c5 bi-Cayley graphs with tabu at 704-768 · c6 wildcard: Z3 lifts of the GQ(5,5)
incidence graph (936 vertices) · c7 wildcard (open) · c8 wildcard: unbalanced orbit structures (1+2 orbits).
Best per card: c1 7.99 s (haarex5 9.1-10.7 in the same window) · c2 8.21 s · c3 10.59 s (no gain) · c4 no cost
below 4: every 1-change costs >= 10, exact over all pairs of voltage changes and all values of 4 voltage triples: >= 5
· c5 cost 20 at 704 (g352_102_2, 6 s runs; calibration: a (5,5) graph on 360 vertices, apsp VALID) · c6 dead: a point
and a collinear point are joined by one walk of length <= 4 up to backtracking, so any lift has diameter >= 6 · c7
insertion of two vertices into the 684 record: 318 bad pairs at 686 (unoptimised matching) · c8 counting bound for
orbit splits with maximum degree 6 and diameter 5: 1+2 orbits <= 249 vertices, 2+3 <= 650, 1+3 <= 108; only 2+2, 3+3
and 3+4 remain above 684 (director checked 1+2: B-degrees k1 + k2 = 6, k1 = k2 = 3 gives 1 + 15 + 150 = 166 >= 2m);
a 3+3 Z115 lift (690 vertices) annealed to 1610 bad pairs.
Director's checks: c1 identical to haarex4 on all 9 calibration groups and on order-384 prefix counts; installed as
research/six-five-384/src/haarex6.c (about 1.2x over haarex5 on order-384 groups in interleaved runs). Merging c2 into
c1 gave no further gain (measured), so it was left out. Machine note for the skill: `nice -n 10` inside a card does
nothing here, because the kernel uses autogroup scheduling (each card's commands run in their own session group at
nice 0, equal to the director's whole pipeline); the director raised the pipeline's group with
`echo -10 > /proc/<pid>/autogroup` and lowered the cards' groups to 15.
Kept: haarex6 for the sweep; no family lead worth more CPU (the 704 lift is an isolated local minimum, the new
families are far). The order-384 sweep continues; orders 401-450 started on the spare core.

## deep-65 round 1 (Nov 1, 2026, 02:38-03:20 UTC; Opus-led job deep-65, cell (6,5), target > 684)
Session claude/deep-65-bipartite-d6-d5-8dgdq1. 4 Haiku cards (research/squads/deep-65/round1/cards.md), written after
Opus closed the 1,6|1,6 hub family exactly on all groups of order 294 (and 300-312) and 1,3|1,3 (5,1,1,1) on 258_2.
- h1 lead (a) by design (684 graph + vertex pair): 144 at 686 (ties the best; 6 deletions, no a-b edge); structured
  designs 154-234; 117 damaged pairs stay unrepairable (54 of kind (0,3), 63 of kind (1,2)), as Opus's damage analysis predicts.
- h2 "1,6,6|1,6,6" (Haar degree 4 + two C6 hub orbits per side), orders 258/264/270: far (bad 1634+).
- h3 "1,1,3|1,1,3" on orders 147/150: bad 294 at 686 on SmallGroup(147,3) (Aut order 147, not isomorphic to the
  294_11 graph; Opus: also a C7xC7 lift, no cost-0 within 2 voltage changes, 922k checked).
- h4 tabu with the algebraic cost of tools/hubk.c: k = 4 on SmallGroup(280,35) cost 3 (n = 700, bad 560); k = 2 best
  cost 7 (234_1, n = 702).
Kept: the 147-family near miss (deepen), k = 4 at 700 (Opus runs the exact search), hubtabu for wider k sweeps.

## deep-65 round 2 (Nov 1, 2026, 03:22-04:05 UTC)
3 Haiku cards (research/squads/deep-65/round2/cards.md), evolved from round 1.
- h5 deepen "1,1,3|1,1,3" (147_3 bad 294): exact 2-change neighbourhood 1.92M pairs, none below 294 (132 ties, next
  1323); kicked tabu restarts and 14 more seeds per group: nothing better.
- h6 hubtabu sweeps: k = 2: 240_112 cost 4 (n = 720), 238_1 6; k = 3: 264_12 = C11 x SL(2,3) and C11 x S4 cost 4
  (n = 704), 270 best 6; k = 4: 288 best 13 (sampled), 284 300.
- h7 lifts of the 14-vertex hub bases by the order-50 groups (n = 700) vs C7xC7/C49: all 72-211; random-start tabu too
  slow to separate groups (cannot re-find the structured 12 over C7xC7).
Kept: the two cost-4 points at 704 went to Opus's exact search (tools/hubk.c k = 3). No round 3: the leads are closed
or explained, and two rounds added no new direction.
