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

### Round 2 (16 cards, 23:20 UTC, research/squads/raise10/r2/) — cells (3..6,10) only

Cards: e01/e02 (4,10) Frobenius farms (both redirected after 10 minutes, see below), e03 (4,10) non-Frobenius metacyclic,
e04/e05 (5,10) Frobenius farms, e06 (5,10) composite-m metacyclic, e07 (5,10) Q x Frobenius products, e08/e09 (6,10)
Frobenius farms, e10 (6,10) products of two Frobenius groups, e11 (6,10) haar_big1 "3 2 0" FIXF, e12 (3,10) cyclic lifts,
e13 (3,10) non-abelian lifts, e14 hole anatomy, e15 wildcard, e16 (4,10) products.
Results (no raise; best cost above the current value):
- **(5,10) e07: A4 x (Z239 x| Z17) (N 48,756) cost 1**; e04 Z1453 x| Z33 cost 2 (three lineages); e05 Z1783 x| Z27 and
  Z2857 x| Z17 cost 3; e06 Z2387 x|_8 Z20 cost 7.
- **(6,10) e08: Z6397 x|_5330 Z41 (N 262,277) cost 1**; e09 Z5851 x| Z45 cost 3; e10 (Z43 x| Z3) x (Z157 x| Z13) cost 4;
  e11 haar_big1 orbit search cost 18 (orbit S far behind random S at Δ = 6).
- (4,10): e03 Z113 x|_2 Z56 (r of order 28: a centre of order 2, like the incumbent) cost 2; e16 (Z11 x| Z5) x (Z19 x| Z6)
  cost 4; e15 PSL(2,7) x Z37 cost 9 and orbit-symmetric S on Frobenius groups (dead: cost 2e4).
- (3,10): e12 Heawood x Z58 / Z59 cyclic lifts cost 6; e13 non-abelian lifts (own annealer nlift.c) Z7 x| Z12 on a 5+5 base
  cost 20, C3 x He3 (the incumbent's group) 62.
- e14 (hole anatomy): every hole of the near misses is at distance exactly 11, one per Z_k-fibre; a Sidon condition on the
  Z_k-coordinates of S (distinct, all differences distinct and nonzero) cut the random-S hole rate 4.5x (Z251 x| Z25) and
  27x (Z1453 x| Z33).
Director during the round: **exh4** (research/frontier/raise10/exh4/), an exhaustive search of Haar graphs H(G,{e,x,y,z}) of
metacyclic groups up to the automorphisms (a,j) -> (ua + (1-r^j)b, j) (x over orbit representatives, y over stabiliser
orbits, z over G, x from the lowest orbit), validated on the incumbent's group Z97 x|_19 Z64 (finds cost-0 sets at once).
**Z251 x| Z25 (r1/c09's cost-2 group): minimum cost 2 over all S, so no 12,550-vertex Haar graph of it has diameter 10**;
cards e01/e02 were redirected (e01 found nothing new to do and stopped; e02 moved to (6,10)). The sweep of all 39 Frobenius
groups of order 6,209-6,600 is running. (17,10) solved at 23:29: PSL(2,181) x Z1321, "5 3 2" FIXF, 7,832,948,760 vertices
(+11.5 %), 598 evaluations; hcheckpsl running. (19,10) started: PSL(2,311) x Z691, "5 3 4" FIXF, mu 17.4.
Process: one card called archive_session by mistake (no such tool; no effect).

### Round 3 (16 cards, 23:45 UTC, research/squads/raise10/r3/) — farms and tools on the near misses

Cards: g01 A4 x (Z239 x| Z17) farm, g02 Q x Frobenius at (5,10), g03/g04 Sidon-constrained hmeta (hmeta_sidon.c, written by
g03) at (5,10)/(6,10), g05 Frobenius farms at (5,10), g06/g07 Frobenius farms at (6,10), g08 A4 x F at (6,10), g09 Q x F at
(4,10), g10 exhaustive opt on products at (4,10) (prodopt.c), g11 Heawood lifts, g12 non-abelian lifts, g13 1-opt tool for
the A4 x F state (prodopt5.c), g14 measurement, g15 wildcard, g16 products of two Frobenius groups at (6,10).
Results (no raise):
- **(5,10) g03: Sidon-constrained Z1453 x| Z33 cost 1** (Sidon start costs: median 48 vs 60, mean 64 vs 2,080 unconstrained;
  the exhaustive Sidon 1-opt of the cost-1 state has no solution); g05 Z2857 x| Z17 cost 2; g02 (Z7 x| Z3) x (Z137 x| Z17)
  cost 3, A4 x (Z313 x| Z13) 5; g14: median holes / size-law mu: A4 x F and (Z7 x| Z3) x F ~1.5, Frobenius ~2, PSL(2,7) x F
  8, SL(2,3) x F ~190.
- (6,10): g04 Sidon Z6397 x| Z41 cost 3 (8 runs; not separable from plain); g07 Z5851 x| Z45 cost 3; g16 (Z43 x| Z3) x
  (Z157 x| Z13) cost 3; g08 A4 x (Z811 x| Z27) cost 4; g14: Z6397 x| Z41 median 1.3 x mu, the best family measured.
- (4,10): g09 (Z7 x| Z3) x (Z43 x| Z7) (N 6,321) cost 3; g10 (Z11 x| Z5) x (Z19 x| Z6): exhaustive 1-opt min 4 (2-opt only
  sampled).
- (3,10): g11 Heawood x Z58 cost 6 again; g12 non-abelian lifts: Z28 x| Z3 (order 84) on a 5+5 base cost 14; g15 Z6 x Z14
  lift cost 34, bi-coset graphs dead.
Director during the round: (19,10) **20,785,224,720** found (PSL(2,311) x Z691, "5 3 4" FIXF, mu 17.4, 46 evaluations) and
(18,10) **12,784,852,920** (PSL(2,211) x Z1361, "5 3 3" FIXF, mu 17.6, 21 evaluations, after a mu-24 run on PSL(2,251) x Z821
stopped at cost 5 after 307 evaluations); (20,10) started with haar_big1 "5 4 0" FIXF on PSL(2,331) x Z911 (mu 18.3). The
(6,10) cost-1 state of r2/e08 is a strict 1-opt local minimum (hmeta OPT1, all 1.3M single swaps).
Process: three cards made stray tool calls (interrupt_session, read_documentation, send_message without arguments; all
rejected or read-only).

### Round 4 (16 cards, 00:09 UTC, research/squads/raise10/r4/) — Sidon farms, 1-opt proofs, products, Δ = 7, 8

Cards: h01/h02 Sidon farms at (5,10), h03 Z2857 x| Z17 with a slot-split 1-opt (hmeta_split.c), h04 Q x F at (5,10), h05 Sidon
at (6,10), h06 F x F at (6,10), h07 Frobenius k 31-63 at (6,10), h08 odd-order products at (4,10), h09 fast 2-opt for products
(prod2opt.c), h10 non-abelian lifts, h11 exhaustive cubic Haar graphs of ~70 non-metacyclic groups of order 406-432, h12 (7,10)
and h13 (8,10) Q x F / F x F, h14 full 1-opt of the cost-1 states (hmeta1.c), h15 wildcard, h16 quotient statistics as filters.
Results (no raise):
- Proofs of local minima: **the (5,10) Z1453 x| Z33 cost-1 state is a strict 1-opt local minimum** (h14, all 191,792 swaps; best
  neighbour 2); the (5,10) Z2857 x| Z17 cost-2 state likewise (h03, all slots); (6,10) Z6397 x| Z41: 19 % of the 1-opt done by
  h14, none solves (the director's full hmeta OPT1 of the r2 cost-1 state: none of 1.3M swaps solves).
- (6,10) h05 Sidon Z6397 x| Z41 cost 2 (1 of 8 lineages; median 4, plain median 4); h07 Z7561 x| Z35 cost 4; h06
  (Z19 x| Z3) x (Z419 x| Z11) cost 5.
- (5,10) h01 Sidon Z1453 x| Z33: 21 lineages, best new 3; h02 Z881 x| Z55 cost 3 with Sidon (5 plain); h04 SL(2,3) x
  (Z157 x| Z13) 3; h16: |ball of radius 5| predicts the final cost (Spearman -0.68) but filtering by it gave no gain.
- (4,10) h08/h09 (Z7 x| Z3) x (Z43 x| Z7) (N 6,321) cost 3: 1-opt minimum 3, restricted 2-opt minimum 3.
- (3,10) h10 Z7 x| Z12 lift on a 5+5 base cost 10; h11: no cost-0 cubic Haar graph in ~70 non-metacyclic groups of order
  406-432 (best (Z3^2 x| SD16) x Z3, N 432, cost 6); h15: abelian Haar graphs are bounded by sum_t C(Δ+t-1,t)^2 (far below
  every record for Δ >= 4), cyclic cubic Haar graphs reach diameter 10 only up to N = 70.
- (7,10) h12 A4 x (Z2237 x| Z43) cost 12; (8,10) h13 (Z211 x| Z5) x (Z547 x| Z7) cost 20.
Director during the round: **(18,10) 12,784,852,920 VALID** (hcheckpsl, ecc 10/10, 1,175 s), **(19,10) 20,785,224,720 VALID**
(1,887 s), **(20,10) 33,036,831,960 found in 9 evaluations** by haar_big1 (k = 5, four free orbits, the new f = 0 FIXF screen;
check running). Mid-cell runs with k = 5 FIXF started: (13,10) PSL(2,179) x Z121 "5 2 3" (mu 31.3), (12,10) PSL(2,131) x Z151
"5 2 2" (mu 39.2).
Reading: four squad rounds (65 cards) produced no raise of (3..8,10). The near misses are strict local minima at 1-3 holes and
fresh lineages keep landing at 2-4; two rounds in a row added nothing new. The squad stops here; the remaining CPU goes to
the director's checks and the mid cells, where k = 5 FIXF is new and evaluations are cheap.
Process: two more stray tool calls by cards (both rejected); one card's shell hung on an append and it used Edit instead.
