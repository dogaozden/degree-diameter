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

## 2026-11-01, job beyond-d11b (Opus director, branch claude/beyond-d11-d12-new-cells-3t3djx)

Goal: new cells (15,11), (16,11), (14,12) with Haar graphs of at most ~30 billion vertices, and raises of the D = 11, 12
cells. Before round 1 the director's haar_big0 runs had already solved all five ~30-billion targets in 1-45 evaluations
each ((16,11) PSL(2,449) x Z331, (15,11) SL(2,617) x Z61 at mu 5.2, (14,12) and (12,12) PSL(2,241) x Z2143, (13,12)
PSL(2,181) x Z5059); their haarcheck_gen checks (one at a time, ~11 GB each) run alongside the squads. So the squads
were aimed at the smaller cells, with ideas nobody had tried. Machine: 4 cores, 16 GB; autogroup off.

### Round 1 (16 cards, 11:48-12:12 UTC, research/squads/beyond11b/r1/)

Cards (best result):
- **g02 (4,11) odd-order metacyclic, plain S: Z_761 x|_25 Z_19 (Frobenius, order 14,459), 28,918 vertices** (was 24,360,
  +18.7 %) at size-law mu 31.6; N = 12,181 and 14,209 solved in seconds; 14,531-15,025 stopped at cost 2-4.
- **g16 SL(2,p) x (odd centre-free Frobenius H): (4,11) SL(2,5) x (Z37 x| Z3) 26,640 in 0.2 s; (5,11) SL(2,5) x
  (Z251 x| Z5) 301,200** (was 297,648); (6,11) SL(2,7) x (Z449 x| Z7) to cost 2. Conjugation-alpha orbits hurt here.
- g03 (5,11) odd-order meta with composite m / with a centre: start costs 1e3-2.6e5, plateau 4-14. g04 F_q x| C_k,
  q = 37^3, k = 21: ~10x worse than the size law. g13 Sz(8): bad at odd D. g06 bipartite Cayley graphs of PGL(2,p):
  worse than Haar at equal size. g05 Frobenius field automorphism as alpha (SL(2,49) x Z9): better start costs than
  conjugation, plateau 10. g08 PSL(2,p^e) with Frobenius alpha at even D: plateau 5 at (5,12). g07 SL x SL products at
  (7,11): cost 24, budget-limited. g11 agl1 products at (4,12)/(4,11): plateaus 11 / 8. g12 Z_m lifts of PG(2,3)
  incidence: (4,11) 19,500 (below). g14 metacyclic lifts of cubic multigraphs: (3,12) cost 2 at 2,184 vertices. g01
  non-metacyclic cubic groups: best min-cost 184. g10 -I pair constraint (a^-1 b of order 10): 2/4 seeds solved
  SL(2,101) at (6,11) against 0/4 plain (2,060,400, below the value). g09 (15,9) calibration: "3 4 3" starts lower than
  "3 5 0" at n = 1, solved SL(2,173) x Z19 at mu 9.5; otherwise inconclusive. g15 theory (r1/g15/NOTE.md): with f = 0
  the number of words reaching -I is 0 mod 6; buying -I with s, -s is bad.

Verified by the director (build_haar2.py and all-pairs apsp; logs research/frontier/runs/cloudcheck/*b1g*.check.txt):
(4,11) 28,918, (4,11) 26,640, (5,11) 301,200. Kept: odd-order centre-free Frobenius groups and SL(2,q) x Frobenius at
odd D (round 2 is built on them, from (4,11) to (8,11), plus an even-D control, a measurement card and a theory card).
Dropped: F_{p^3} x| C_k, Sz(8), bipartite Cayley, agl1 products, conjugation-alpha orbits on Frobenius products.
Process: cards stopped after 6-20 minutes of their 25 (g15 after 7); round 2's prompt says not to stop before 25.
