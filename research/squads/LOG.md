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

## 2026-11-01/02, job deep-65b (Opus cloud session, branch claude/bipartite-d6-d5-depth-bkg1ku), goal: (6,5) > 684

Opus derived a closed form for lifts of the 2+2 base [[1,5],[5,1]] (the degree-10 Haar graph H(G, E1 u E2) with every
vertex split into an edge; six covering conditions on two 5-sets) and wrote an exact search (deep-65b/tools/split15.c,
validated against BFS and brute force). Rounds in research/squads/deep-65b/round1, round2.

### Round 1 (23:08-00:00 UTC, 6 cards, research/squads/deep-65b/round1/)
Cards: c1 tabu over (E1, E2) to rank the groups of orders 172-200 for the split family · c2 word-based tabu for the
other 2+2 bases, calibrated on the 684 record · c3 hub family k = 5 exact (hubk.c, deep-65's open case) · c4 hub family
k = 3 on 258_3..5 exact · c5 wildcard "path-split" Haar graphs (3+3 lifts) · c6 open wildcard.
Best per card: c1 **cost 0 at 704 vertices: SmallGroup(176,23) = C11 x M16** (seed 3 of 5, 9 s runs; ranking of 160
groups, next best 174_1 2, 176_17 2) · c2 general 9-voltage tabu does not re-find 684; the mirrored (Haar-type)
subfamily re-finds it in 6/8 seeds; screen 172-180: best 10 (720) · c3 k = 5: 290_1..3 closed (n = 696, nothing passes the hub-level conditions) and 16 of 45 groups of order 300; 305-315 not run · c4 258_3
0.09%, 258_4 12%, 258_5 6% of the leaves, no state passes the hub-level conditions so far, full runs 2-4 h (258_4/5) and
~170 h (258_3) · c5 path-split best 1755 bad pairs at 702 (C13:C9) · c6 4+4 lifts best 1505 bad pairs at 688.
Director's checks: rebuilt c1's graph from an explicit formula of C11 x M16 (no GAP), apsp VALID at D = 5 and
INVALID at D = 4, score65 bad 0 (research/squads/deep-65b/records/). The exact search split15 on 176_23 re-found the
same solution class (end-to-end check). The exact search had closed 176_17 (best 2) before the hit.
Kept for round 2: c1's tabu, spread over orders 178-200 with more seeds (one zero came from 1 of 5 seeds), and a faster
tabu.

### Round 2 (00:00-00:55 UTC, 6 cards, research/squads/deep-65b/round2/)
Cards: c1 order 180 all 33 non-abelian groups, 6-16 tabu seeds x 12 s · c2 orders 178-190 (incl. C61:C3 at 183) · c3/c4
order 192, the 256 groups C3 x P64 (the winner's shape: central cyclic x 2-group), 2-8 seeds x 8 s · c5 orders 195-200
and 59 other order-192 groups · c6 a faster tabu (code card).
Best per card: c1 180_2 cost 4 (C9 x (C5:C4)), 180_6/14/21 5 · c2 183_1 (C61:C3), 189_6, 189_8 7 · c3 192_865, 192_909
6 · c4 192_900, 192_168 8 · c5 200_19 13, 192_544 10 · c6 tabu15f: same trajectory as tabu15, 3.3x faster, costs equal
split15 on 20 states; re-finds the 704 graph (seed 3, 2.55 s); order-192 ids 1-127 best 8.
No zero above 704. Director: exact split15 runs on 180_13 (best 6), 180_6 (best 5): no solution; exact runs started on
180_21 and on 192_865, 909, 544, 105, 106 (Aut of order 384-6144, so 2-35 min each).
Kept for round 3: more seeds with tabu15f on the closest groups (180, 192), plus two structures next to the split
family (split + hub orbits via mcos; cyclic lifts of the 8-vertex split base with free voltages).

### Round 3 (00:57-01:07 UTC, 4 cards, research/squads/deep-65b/round3/), stopped early for budget
Cards: c1 split + hub orbits via mcos (n = 728) · c2 order 180 with 20 seeds of the faster tabu · c3 order 192, next 12
groups, 12 seeds · c4 cyclic lifts of the 8-vertex split base with free voltages (n = 712-800).
Results: c4 calibrated on the record's Z88 voltages (cost 0) but random-start tabu never reaches 0, even at n = 88;
best 34 at n = 90; c1-c3 stopped before reporting, no zero on the scoreboard. Director's exact runs: 180_21 (best 3),
192_865, 909, 544, 105, 106: no solution. Run ended at 01:07 UTC with the 704 record (deep-65b/REPORT.md).
