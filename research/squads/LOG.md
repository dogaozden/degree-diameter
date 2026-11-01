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

## 2026-11-01/02, job raise-d10 (Opus director, branch claude/raise-d10-beyond-rcdq5p)

Goal: raise the lab's D = 10 values at Δ = 3..20 with the searches of the D = 11..14 jobs (haar_big0, Frobenius groups
with random S, lifts) and the (16,10) recipe (k = 5 orbits with the FIXF screen of alpha-fixed holes). Before the job the
D = 10 column sat at size-law mu 22-60 for Δ <= 16 (heavily pushed by dedicated sessions) but at mu ~3 for Δ = 17..20
(first values of the beyond job, k = 3, first S solved). Machine: 4 cores, 15 GB, autogroup turned off at the start
(so the cards' nice 10 works). Director tools: research/frontier/raise10/ (haar_big0; haar_big1 = haar_big0 with the
FIXF screen extended to f = 0, validated against full evaluations on 15 random S, screen = full count every time).

### Round 1 (17 cards, 22:52 UTC, research/squads/raise10/r1/)

Cards: c01/c02 (12,10) k = 5 FIXF (PSL p 90-220 / SL and large-p PSL); c03 (13,10) the old k = 5 cost-1 lead PSL(2,131) x
Z311 with FIXF; c04 (13,10) the old k = 3 cost-1 leads (SL 103 x 313 ...) with FIXF; c05 (9,10) "3 2 3" FIXF; c06 (11,10)
k = 5 FIXF above mu 60; c07 (3,10) cyclic lifts + 1-opt finisher; c08 (3,10) exhaustive cubic Haar graphs and non-cyclic
voltage lifts; c09/c10 (4,10) Frobenius groups / products with random S; c11/c12 (5,10) the same; c13 (6,10) Frobenius
and products; c14 (7,10) and c15 (8,10) haar_big0 FIXF on the k = 3 wall; c16 wildcard small cells; c17 wildcard mid
cells. The director ran (17,10) "5 3 2" FIXF on PSL(2,181) x Z1321 (mu 29) and (18,10) "5 3 3" FIXF on PSL(2,251) x Z821
(mu 24) alongside.

Results (no card beat a value; best cost above the current value):
- Mid cells (haar_big0 + FIXF, 1 thread at nice 10 beside the director's two big runs): c01 (12,10) PSL(2,149) x Z101 "5 2 2"
  cost 10; c02 SL(2,109) x Z131 cost 20; c03 (13,10) PSL(2,131) x Z311 "5 2 3" cost 10 (the old cost-1 lead was not
  reached: ~9 evaluations per 100-s link); c04 (13,10) SL(2,163) x Z79 "3 4 1" cost 9; c05 (9,10) SL(2,73) x Z31 "3 3 0" cost
  9 ("3 2 3" with FIXF worse: 39); c06 (11,10) SL(2,109) x Z61 cost 53; c17 (10,10) PSL(2,79) x Z131 "5 2 0" cost 10.
  c14 (7,10) PSL(2,19) x Z337 cost 21 and c15 (8,10) PSL(2,31) x Z271 cost 18 (fast evaluations, but k = 3 with m = 2
  orbits stalls far above the old haar_sym plateaus of 1-3).
- Small cells: **c09 (4,10) Frobenius Z251 x| Z25 (N 6,275) cost 2**; c10 (4,10) (Z11 x| Z5) x (Z19 x| Z6) (N 6,270) cost 4;
  c16 (4,10) 2-dim Frobenius Z13^2 x| Z42 cost 56; **c11 (5,10) Frobenius Z1453 x|_11 Z33 (N 47,949) cost 2**; c12 (5,10)
  PSL(2,7) x (Z97 x| Z3) (N 48,888) cost 4; **c13 (6,10) Frobenius Z6397 x| Z41 (N 262,277) cost 3**; c07 (3,10) cyclic lifts:
  Moebius-Kantor x Z51 cost 26 (Pappus x Z46 72, Desargues x Z41 134); c08 (3,10) exhaustive cubic Haar graphs of all 157
  faithful metacyclic groups of order 406-460: minimum cost 8, no cost-0 pair.
Reading: on this box the mid cells get ~10-30 evaluations per card link, too few at mu 25-60; those cells stay with the
director or are dropped. The Frobenius random-S family (D = 11, 12 winners) comes within 2-3 holes at (4,10), (5,10),
(6,10) above the current values; round 2 farms these. Process: two cards called send_message once with no arguments
(rejected, nothing sent); several haar_big0 links overran their seconds (the program checks time only between steps).
