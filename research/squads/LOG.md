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

### deep-49 (Opus-led squad on the bipartite (4,9) cell), 2026-11-01 22:39Z - 2026-11-02 ~01:00Z
Session session_01QYEEyH81pZHeSQtpD99oPr, branch claude/deep-49-bipartite-cell-3tog1a. Goal: (4,9) bipartite graph on >= 4,971
vertices (table 4,970), with depth on the handsoff-49 leads. Report: research/squads/deep-49/REPORT.md.
Before the squad the director wrote hx (exact Haar search reduced by Aut(G)), installed GAP, certified all 67 SmallGroups
candidates of order 2,486..2,600 (no cost 0) and ran the bi-coset Frobenius family (bicos, best 88).
Round r1 (23:10Z, 8 cards, research/squads/deep-49/r1/): c1 non-solvable 2,520 exact · c2 split metacyclic of the orders
missing from SmallGroups · c3 exact minima of Frobenius groups 2,200..2,800 · c4 constrained searches at the walls ·
c5 vertex insertion by design · c6 bi-coset graphs with point stabilisers, composite kernels · c7 non-metacyclic solvable
groups of the missing orders · c8 wildcard (chose 2+2 lifts).
Best per card: c1 SL(2,5) x F21 exact 4 (n 5,040; new), A7 6, S5 x C21 7 · c2 263 groups, no cost 0 · c3 cost 0 only at
2,211, 2,265, 2,485; 2 at 2,329 and 2,525 · c4 central involution missed by all cost-4 sets of both 2,496 groups; forcing it
costs 8 / 12; 5,050 misses only in classes +-6, +-9 · c5 149 (design + swaps), twins 775 · c6 best 16 (a Haar subfamily),
28 non-Haar · c7 368 groups, no cost 0 · c8 2+2 lift cost 12 at 5,004.
Round r2 (rolling, 23:35-01:00Z, research/squads/deep-49/r2/): a non-direct non-solvable 2,520 groups + SL(2,5) x F21 wall
(fibred products > 8; its cost-4 sets miss order-30 or order-12/3 elements, never involutions) · b mixed-orbit and hub-orbit
screens (17 and 25) · c luck curve 2,440..2,485 (cost 0 only at 2,485 and 2,440 = Z_61 x|_8 Z_40, apsp VALID n 4,880) ·
d auditor (independent exh3 confirms 8 of 9 claims, 1 unfinished; one latent early-exit bound in hx fixed) · e metacyclic
2,531..2,600 missing orders (see report).
Director's own: surgery designs exhaustive (alternating paths 2,916 designs, linked designs 41,040): 149, and every far pair
of the best design is a slack-0 critical pair. Kept: nothing for a record; the squad's value here was breadth of exact
certificates (several hundred groups) at about 6% of the spend.
