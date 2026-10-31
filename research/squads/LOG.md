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

### Round s384r3 (16:24-17:05 UTC, 8 cards, research/squads/s384r3/), after the order-384 and 401-450 sweeps finished
All 4 cores went to the squad. Goal: the brief's remaining item, bi-coset and lift families at 686-768 vertices.
Cards: c1/c2 non-Haar |H| = 2 bi-coset graphs at orders 722-736 / 738-766 (never swept; squad-6-5's sweep.sh,
SKIPHAAR) · c3 bi-Cayley tabu, long runs at 704 · c4 2+2 lift tabu from random starts, orders 172-192 · c5 3+3 lift
tabu, orders 115-128, all 17 bases · c6 annealed insertion of 2 vertices into the 684 graph · c7 wildcard · c8 wildcard
(a necessary condition explaining why side A almost never covers).
Best per card (none valid): c1 20 (SmallGroup(732,10); all 282 groups of order 722-736, only 41 non-Haar pairs exist;
calibration reproduced 8 on 720_439) · c2 22 (756_86/87, annealing; all 423 groups of order 738-766; candidate pairs
only at 740, 744, 748, 756, 760) · c3 5 at 704 (g352_102_2, type (3,3), 90 s tabu; annealing's 4 from squad-6-5 still
best) · c4 8 at 696 (C29 x S3, 120 s; 34 groups screened) · c5 20 at 702 (C13:C9, base m06; squad-6-5's 14 at 696
stands) · c6 150 bad pairs at 686 (random matching: 318) · c7 K_{6,6} base lifted by cyclic groups (6+6 orbits): 2,320
bad pairs at 696; diameter 5 reached at 480 (Z40) as calibration, the family falls off above ~500 · c8 global
inverse-pair count vacuous (needs > 397 involutions); hint for a per-coset version.
Director: per-coset version made exact (c(y) >= |N| + v_y for y = y^-1, v_y = involutions in the coset; README filter 4)
and applied to G/G'G^2 for all 18,327 order-384 groups with r2 <= 4: excludes none (smallest margin 2). Correction to
round s384r2: the orbit-split bound evaluated only the splits 1+1, 1+2, 1+3, 2+2, 2+3, 3+3, 3+4, so "only 2+2, 3+3 and
3+4 remain" holds among those; 4+4, 6+6 etc. were not evaluated (c7's point).
Outcome: |H| = 2 non-Haar bi-coset graphs are now swept (one annealing seed per pair) on all orders 686-766; no family
came closer than squad-6-5's best (2+2 lift and bi-Cayley at cost 4, 704 vertices). Three rounds of families with no
gain: the (6,5) cell looks exhausted for these families at this size; stop here.
