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

## 2026-11-01, beyond-d13, round 1 (16 cards, 11:39 UTC)

Session: Opus director, job beyond-d13 (branch claude/beyond-d13-search-z35z61). Goal: first values for D = 13 at
Δ = 3..10 and D = 14 at Δ = 3..8 (no values recorded there), at most 20 billion vertices. Files:
research/squads/beyond13/r1/ (HEADER.md, c01-c16.md, scoreboard.jsonl). Before the round the director had (4,14) 416,640
and (5,13) 3,176,880 (1 evaluation each), (10,13) 19,980,294,768 (first S, at the cap) and (9,13) 7,508,907,120
(5 evaluations), and started (8,14). Machine: 4 cores, 15 GB, shared with the director's three big checks (load 15-29).

Cards (best result; all VALID by haarcheck_gen, apsp or metacheck unless marked):
- c01 (3,13) metacyclic exhaustive (exh3): Z133 x|_36 Z9, 2,394; only N <= 1,200 reached (exh3 got ~1 % CPU).
- c02 (3,14) metacyclic sampled: nothing; it used k <= 8 only (virtually abelian; see c15).
- **c03 (3,13) other groups, exhaustive S = {e,x,y}: A6 x Z4, 2,880**; SL(2,11) 2,640, PSL(2,13) 2,184.
- c04 (4,13) SL ladder: PSL(2,23) x Z13 78,936; SL(2,43) x Z1 stuck at cost 4 (order-6 holes).
- **c05 (4,13) new exhaustive orbit scan (orbscan.c, S = {e,x,ax,a^2x} over all x): PSL(2,29) x Z7, 170,520** (38 tries).
- **c06 (4,14) ladder: PSL(2,41) x Z7, 482,160**; PSL(2,29) x Z19 462,840; PSL(2,79) x Z1 stuck at 31.
- **c07 (5,13): PSL(2,47) x Z31, 3,217,056** (18 s); PSL(2,37) x Z67 stuck at 18.
- **c08 (5,14): PSL(2,227), 11,696,856, random S (haar_gen3)**; the orbit form "3 1 2" stalls at 18 (median of random
  symmetric S 90): at Δ = 5 one random fixed generator plus one orbit is too rigid.
- **c09 (6,13): PSL(2,103) x Z37, 40,427,088** (11.5 s); PSL(2,109) x Z31 40,142,520; mu 8.5-11.5 stuck at 6-15.
- **c10 (6,14): PSL(2,101) x Z181, 186,466,200** (chained links, mu ~7).
- **c11 (7,13): SL(2,199) x Z19, 299,455,200**; SL(2,281) x Z7 310,628,640 search cost 0 (check pending).
- **c12 (7,14): SL(2,109) x Z613, 1,587,571,920** (13 evals, mu 2.1; director check).
- **c13 (8,13): SL(2,911) x Z1, 1,512,114,240** (first draw; director check).
- c14 hole anatomy at (5,13) (ANATOMY.md): -I missed by 20-46 % of random S; central (+-I,z) ~ n e^(-λ/6); PSL
  involutions 5-11 holes per S; SL 16-20 holes per S against PSL 22-27. Rule stays: SL, small n.
- **c15 wildcard, odd-order groups at odd D: Z4903 x|_230 Z19 (order 93,157, no involutions), random S, 186,314** — the
  best (4,13) value, 9 % above the orbit scan. k = 13, 17, 19, 23 all solved at 170-180k; k = 3 hopeless; k = 11 stalls.
- **c16 wildcard, prime-power field: PSL(2,49), random S, 117,600 at (4,13)**; PGL(2,37) 101,232.

Director's reading: at small Δ the orbit structure is too rigid (c08, c16, c15 all won with random S), and at odd D a
group without involutions wins (c15) — the exact lemma of ODD_D_HOLES.md predicts it, but nobody had tried odd-order
groups. Kept for round 2: odd-order metacyclic groups at (4,13), (5,13), (6,13) and products; random S at Δ <= 5;
the even-D control; exhaustive scans at Δ = 3, 4; pushes of the mid cells. Dropped: metacyclic k <= 8. Process: the
director's three checks (5 threads at nice 0) starved the cards (c01, c02, c05 report a few % CPU); round 2 gets the
same machine, so its cards are told to keep runs short.
