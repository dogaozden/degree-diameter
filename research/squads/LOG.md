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

## 2026-10-31, handsoff-49, round 1 (goal: bipartite (4,9) > 4,970; hands-off Opus coordinator, Haikus do the work)

Session session_01QYEEyHVSftkeoMe7ftkrav, branch claude/handsoff-49-bipartite-search-hy5axz. 8 Haiku workers, 21:42 to
about 23:55 UTC, each owning one card for up to 2 hours (research/squads/handsoff-49/cards.md, scoreboard.tsv, w1..w8/).
Cards (best n / cost; cost = the worker's own count, far pairs in brackets where known):
- w1 Haar, non-metacyclic groups: 5,040 / 6 (A_7; exhaustive over all Haar sets of A_7: minimum 6, ruled out). Others
  floor 7-10. Low cost tracks a small centre and a small abelianization. 82 min.
- w2 Haar, all metacyclic groups of order 2,486..2,600 (1,779 split + 686 non-split): 5,050 / 2 (known), 4,992 / 4
  (104 24 7 known; 208 12 3 new), then 6. 107 min.
- w3 lifts of W(3) (80 vertices) over groups of order 63-80: 5,040 / 906; valid only up to 3,200 (Z_40). 85 min.
- w4 lifts of H(3) (728 vertices): dead by w4's own proof (girth 12 puts fibre-mates at distance >= 12); redirected at
  22:45; best 6+6 random base over meta 13 32 5: 4,992 / 76. 129 min.
- w5 lifts of 5+5..8+8 bases: these floor at 100+; 2+2 base [[2,2],[2,2]] over meta 13 96 5: 4,992 / 4 [2,496]. 109 min.
- w6 surgery on the valid 4,970 graph: 4,972 with 160 far pairs; every edge is critical for 168-179 pairs, 2-switches
  cost ~350. Handed back early twice, resumed. 
- w7 bi-coset graphs: PSL(2,25), |H| = 3: 5,200 / 30 (exact minimum); PSL(3,3) 5,616 / 64. Perfect groups best. 74 min.
- w8 wildcard: 2+2 lift over AGL(1,13) x Z_8: 4,992 / 15 [9,360]; lifts of the (4,5) 162 graph stall at ~2,150. 99 min.
No valid graph above 4,970. Kept: small centre + small abelianization (round-2 cards w10, w15, w12), bi-coset graphs of
perfect groups (w9, w14), exhaustive certification (w11), the cost-4 wall at 4,992 (w13), quotients of the 4,970 graph
(w16). Round 2 runs as a rolling queue: each finished worker is replaced at once by a new card.

## 2026-10-31/11-01, handsoff-49, round 2 (rolling queue, 23:03 to 03:10 UTC)

Same session. Each finished worker was replaced within minutes by a card built from round-1 results (18 Haikus, w9-w26;
cards at the bottom of research/squads/handsoff-49/cards.md). Best per card (n / cost; "exact" = exhaustive):
- w9 bi-coset, larger stabilizers: S_7, H an involution, 5,040 / 15 exact; M_11 38, PSL(2,25) 30, A_8 168.
- w10 centreless, small abelianization: S_5 x F_21 5,040 / 8 (exact by w21); others 22-2,296.
- w11 exhaustive certification: 33 metacyclic groups exact (2, 4, 4, 6..10), no cost 0.
- w12 lifts over simple groups, tabu: PGL(2,11) 2+2 5,280 / 64.
- w13 the cost-4 wall at 4,992: central involution far in every state with cost <= 6; workarounds 8-72.
- w14 bi-coset, large simple groups: PSL(3,4) 5,040 / 312 exact; others worse.
- w15 order 2,500 = P x| Z_4: 5,000 / 4 (exact by w23; wall = an inverse pair of order-20 elements).
- w16 quotients of the 4,970 graph (5+5 over 497, 7+7 over 355, 35+35 over Z_71): rebuild it, but plain annealing cannot
  re-find cost 0 on the 5+5 base; re-lifts over bigger groups 82.
- w17 mixed-orbit graphs (regular on A, stabilizers 2/4 on B): A_7 5,040, 15,120 far pairs (worse than Haar).
- w18 auditor: 51 lines re-scored, no VALID above 4,970, 3 bookkeeping slips, certified negatives re-run and matched.
- w19 refinement ladder (Haar optima as k+k lifts over index-k subgroups): every search stays at the Haar start.
- w20 D = 9 abelian-quotient bound (309) and 46 more metacyclic groups certified (832 classes of 2,486..2,520 left).
- w21 exact minima: S_5 x F_21 8, PSL(2,8) x Z_5 8.
- w22 wildcard: compound graphs and mixed bi-Cayley graphs behave like random graphs (34k-82k far pairs).
- w23 order 2,500 group: exact minimum 4.
- w24 optimizer benchmark: a Z_5-symmetric ansatz re-finds the known 5+5 cost-0 lift in 13 of 40 runs (plain: 0 of 3);
  scans of 154 groups with it: best 50, no zeros.
- w25 final audit and summary table; w26 size benchmark (apsp 39 ms at 4,970 vs 3-4 ms at 170/686; 12.8k vs 0.8M Haar
  evaluations per second).
No valid graph above 4,970. Kept for later: the symmetric-ansatz optimizer (w24) on lifts of 5+5 and 7+7 bases, the
unfinished metacyclic certificate (w20/run21.sh). Report: research/squads/handsoff-49/REPORT.md.
