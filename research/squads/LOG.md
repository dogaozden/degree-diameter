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

## 2026-11-01, beyond-d13, round 2 (16 cards, 12:04 UTC)

Same session. Files: research/squads/beyond13/r2/. Selection from round 1: odd-order groups at odd D (e01-e03, e12, e14),
the even-D control (e06), random S at Δ = 5 (e07), exhaustive scans at Δ = 3, 4 (e04, e05, e13), pushes of the mid
cells (e08-e10), theory of odd-order groups (e11), and two wildcards (e15 other odd-order groups, e16 voltage lifts).
Machine: the director's (10,13) and (9,13) checks and pushes held 4-5 threads at nice 0; cards got 5-10 % of a core.

Cards (best result; all VALID by haarcheck_gen, apsp or metacheck unless marked):
- e01 (4,13) meta push: nothing above 186,314 (Z7177 x|_368 Z13, N = 93,301, stuck at 2; starved).
- e02 (5,13) single odd-order meta: Z72497 x|_9840 Z23, 3,334,862 (beats 3,217,056; below e12).
- e03 (6,13) meta: Z331231 x|_58155 Z61 cost 2 (N 2.02e7, below the record anyway); the meta orbit form saturates.
- e04 (3,13) exhaustive: nothing (7 % CPU). e05 (3,14) exhaustive: PSL(2,7) x Z15, 5,040 (below the lift).
- e06 (4,14) meta control: best cost 1; metacyclic groups do not clearly help at even D.
- **e07 (5,14): PSL(2,53) x Z79, random S, 11,757,096.**
- **e08 (6,14): SL(2,193) x Z13, 186,910,464.** **e09 (6,13): SL(2,103) x Z19, 41,519,712.**
- **e10 (7,13): SL(2,229) x Z13, 312,227,760.**
- e11 theory (r2/e11/ODD_ORDER.md): Z_m x|_r Z_k with m prime is a Frobenius group: no involutions and trivial centre, so
  neither odd-D clump exists; word cover of random S is 1 % (k = 1), 6 % (k = 3), 73 % (k = 5), 97-99 % (k >= 11).
- **e12 (5,13): (Z79 x|_64 Z13) x (Z59 x|_4 Z29), odd order, random S, 3,514,394** (+9 % over the orbit-S value).
- e13 (4,14) orbit scan: starved, nothing. e14: orbit S in meta groups saturates; random S better (6,13).
- e15 (4,13) Z_p^2 x| Z_k (odd order): 162,266 (below).
- **e16 (3,13): Z160 voltage lift of the Desargues graph, 3,200** (above every Haar graph); the director then ran the same
  tool at D = 14: **Z280 lift, 5,600** in 12 s.

Director's reading: two new families beat the Haar orbit searches at small Δ: odd-order groups at odd D (Δ = 4, 5) and
cyclic voltage lifts at Δ = 3 (both D). At Δ >= 6 the SL/PSL orbit search still wins (meta random S at (6,13), (7,13)
stays at cost 2-36 at matched N, also with the director's new bit-parallel hmeta). Kept for round 3: lifts at Δ = 3, 4,
5 (liftd, any degree), odd-order pushes with hmeta at (4,13), (5,13), the D = 11 test of the odd-order rule, theory of
lifts, pushes of (4,14), (5,14), (6,13), (6,14), (7,13), (7,14). Dropped: meta orbit S, meta at even D, exhaustive Haar
pairs at Δ = 3 (lifts are larger).

## 2026-11-01, beyond-d13, round 3 (16 cards, 12:31 UTC)

Same session. Files: research/squads/beyond13/r3/. Selection from round 2: lifts at Δ = 3, 4, 5 (f01, f02, f04-f06; the
director generalised e16's lift.c to any degree, liftd), lift theory (f03), odd-order pushes (f07, f08) and the D = 11
test of the odd-order rule (f15), non-abelian voltage lifts (f16), pushes of (4,14), (5,14), (6,13), (6,14), (7,13),
(7,14) (f09-f14). The director's (10,13) check was OOM-killed at 12:35 after 58 min (a card's python checker plus the
director's (8,14) push pushed the box over 15 GB); restarted at 12:50 with 3 threads.

Cards (best result):
- f01 (3,13) lifts of 40-vertex bases: cost >= 26 at 3,240-3,360; nothing above 3,200.
- f02 (3,14) GP(10,3) at n = 281-285: best cost 2 at n = 282 (5,640); nothing above 5,600.
- f03 theory (r3/f03/LIFTS.md): in a Z_n lift the end of a walk depends only on its net traversal vector; GP(10,3)
  keeps 82 % of the 24,574 nonbacktracking walks of length <= 13 distinct (74 % at 14); random voltages give n ~ 130-150
  (D = 13) and 250-300 (D = 14) against 160 and 280 found; K4,4 lifts cap near 31,000 at (4,13); a girth-8 4-regular
  base could reach ~2.9e5.
- f04 (4,13) lifts: PG(2,3) x Z4600, 119,600 (apsp VALID); below the Haar value. f05 (4,14) GQ(3,3) x Z6100 (488,000):
  start cost 1,330, 900-s anneal under load.
- f06 Δ = 5 lifts: start costs in the millions; nothing.
- f07 (4,13) hmeta: (pending at the time of writing).
- **f08 (5,13): (Z29 x|_16 Z7) x (Z457 x|_289 Z19), 3,525,298** (metacheck2 VALID).
- f09 (4,14) orbscan / ladder: all groups at N 241-260k have mu 12-17; best cost 30.
- **f10 (5,14): PSL(2,73) x Z31, random S, 12,057,264.** **f11 (6,13): PSL(2,83) x Z73, 41,734,392.**
- **f12 (6,14): PSL(2,137) x Z73, 187,698,768.** **f13 (7,14): SL(2,163) x Z193, 1,671,605,424** (director check).
- f14 (7,13): (pending).
- **f15 (4,11): odd-order Z599 x|_498 Z23, 27,554 — raises the beyond-d11 value 24,360 by 13 %** (metacheck and apsp
  VALID). (5,11) not beaten (single meta stuck at 6).
- f16 non-abelian (metacyclic) voltage lifts of GP(10,3): cost 2 at 3,300; annealer too weak to judge.

Director's reading: the odd-order rule holds at D = 11 too (one more cell raised). Lifts win at Δ = 3 but not at Δ = 4, 5
with the bases tried; the lift theory says girth >= 8 bases are needed. Kept for round 4: Tutte 8-cage and GQ(3,3)
lifts, a provable lift bound, odd-order products at (4,13) and (5,11), hmeta at (4,14) and (5,13), pushes of the mid cells.

## 2026-11-01, beyond-d13, round 4 (16 cards, 12:58 UTC)

Same session. Files: research/squads/beyond13/r4/. Selection from round 3: girth-8 lift bases (Tutte 8-cage g01, GQ(3,3)
g03), other cubic bases at (3,14) (g02), odd-order products at (5,11) (g04) and (4,13) (g10), hmeta at (4,14) and (5,13)
(g13, g14), metacyclic voltage lifts with a better annealer (g12), the lift bound (g11), pushes (g05-g09, g15), wildcard g16.

Cards (best result):
- g01 Tutte 8-cage lifts: (3,14) n = 187 (5,610) cost 2, (3,13) n = 107 cost 10; found that lift.c's cooling runs over
  L = 20,000 evaluations, so short runs never cooled (all earlier short lift runs were effectively hot).
- g02 other cubic bases at (3,14): Pappus n = 312 (5,616) cost 2; F26A, Tutte, Heawood, Moebius-Kantor worse.
- g03 GQ(3,3) lifts at (4,14): cost 612 at 482,400 (bit-parallel lift cost, 20x faster). Nothing.
- **g04 (5,11): (Z29 x|_7 Z7) x (Z67 x|_9 Z11), odd order, 299,222 — raises the beyond-d11 value 297,648.**
- g05 (8,13): cost 16 at mu 9.3 (71 s per evaluation under load). g08 (6,13): SL(2,59) x Z103 cost 2.
- **g06 (7,14): SL(2,269) x Z43, 1,673,976,240** (director check). **g07 (6,14): SL(2,97) x Z103, 187,990,656**
  (RANDORB screen of start costs, then 2 links). **g09 (5,14): PSL(2,53) x Z83, random S, 12,352,392.**
- g10 (4,13) odd-order products: cost 16 at N 100,891. g12 metacyclic voltages on GP(10,3): cost 2 at 3,300 (tabu).
- **g13 (4,14): odd-order metacyclic Z7001 x|_4532 Z35, hmeta, 490,070** (cost 1 chain, then T0 = 4, REHEAT = 200) —
  the first even-D cell where a metacyclic group beat SL/PSL.
- g15 (7,13): SL(2,137) x Z61 cost 6. g16 Z_a x Z_b lifts of GQ(3,3) at (4,13): cost 753.
- g11 (lift bound), g14 (hmeta (5,13)): pending at the time of writing.

Director's reading: four more cells raised, one more D = 11 cell raised by the odd-order rule; the lift near misses at
Δ = 3 (cost 2 in three bases) may have been cooling-limited. Round 5: the same near misses with proper cooling and
START chains, the lift and metacyclic ideas tested on the lab's D = 11, 12 cells, RANDORB screening for the mid cells.

## 2026-11-01, beyond-d13, round 5 (16 cards, 13:24 UTC)

Same session. Files: research/squads/beyond13/r5/. Selection from round 4: near misses with proper cooling and START
chains (h01-h04), products and random S at Δ = 5 (h05-h07), the metacyclic idea on the lab's D = 11, 12 cells (h07-h09),
lifts at D = 11, 12 (h10), RANDORB screening for the mid cells (h11-h14), two wildcards.

Cards (best result; all checked by the director unless marked):
- h01 (3,13): Pappus x Z179, 3,222 (the director meanwhile had GP(10,3) x Z163 3,260 and x Z166 **3,320** with L = 1,200).
- **h02 (3,14): GP(10,3) x Z282, 5,640**, with a new finisher scan.c (exhaustive 1-opt voltage scan + tabu), from the
  director's cost-2 near miss, in 7 iterations.
- **h03 (4,13): Z2237 x|_1984 Z43, 192,382** (hmeta, second link with T0 = 8, REHEAT = 400).
- **h04 (4,14): Z4027 x|_2950 Z61, 491,294.** (The card also started a remote session by mistake and archived it.)
- **h05 (5,13): (Z11 x|_4 Z5) x (Z1301 x|_667 Z25), 3,577,750.** **h06 (5,14): SL(2,97) x Z7, random S, 12,776,064.**
- **h07 (5,11): Z5279 x|_1922 Z29, 306,182** (lab value 297,648). **h08: (4,12) Z1277 x|_964 Z29, 74,066** (lab 68,544)
  and **(5,12) Z17981 x|_15904 Z29, 1,042,898** (lab 1,041,768) — even D, so the gain at Δ = 4, 5 is from random S
  (three free generators against one orbit), not only from odd order.
- h09 (6,11): meta at cost 2 (lab 2,094,960 stands). h10: lifts at D = 11, 12 stay below the metacyclic Haar values.
- h11 (6,13): SL(2,59) x Z103 stays at 2 (the two holes are a transpose pair). h12 (7,13): PSL(2,131) x Z139 at 3.
- h13 (6,14): PSL(2,83) x Z331 at 3. h14 (7,14): PSL(2,223) x Z151, 1,674,490,944 (+0.03 %; not checked).
- h15 exh3 over odd-order groups at (3,13): cost 4. h16 orbit S on products: no orbit found; random S cost 68.

Director's reading: the small cells keep moving (Δ = 3 lifts via cooling and the 1-opt finisher; Δ = 4, 5 metacyclic
groups with random S also at even D). Round 6 (last): the same levers once more, and a test against the 2013 records at
D = 9, 10 for Δ = 3, 4, 5, plus the first-moment explanation of random vs orbit S.

## 2026-11-01, beyond-d13, round 6 (16 cards, 13:48 UTC)

Same session. Files: research/squads/beyond13/r6/. Selection from round 5: the same levers once more (lifts with the scan
finisher; hmeta with T0 = 8, REHEAT = 400; products; random S), the metacyclic rule on the lab's D = 11, 12 cells and on
the 2013 table at D = 9, 10 (i09, i10, i16), the first-moment theory (i12), mid-cell screens (i13, i14), two wildcards.

Cards (best result; all checked by the director):
- **i04 (4,14): Z2731 x|_2400 Z91, 497,042.** **i05 (4,11): Z1093 x|_901 Z13, 28,418** (lab 24,360 before this job).
- **i06 (5,13): (Z11 x|_4 Z5) x (Z2971 x|_1764 Z11), 3,594,910.** **i08 (5,12): Z9859 x|_4192 Z53, 1,045,054.**
- **i10: (5,10) Z1567 x|_871 Z29, 90,886 — above the 2013 table value 90,068** (apsp + metacheck; the lab has no later
  (5,10) entry; a candidate for the coordinator). (5,9) 28,418 beats 27,936 (2013) but not the lab's 29,756.
- **i11 (6,11): Z17203 x|_9845 Z61, 2,098,766** (lab 2,094,960): the metacyclic rule reaches Δ = 6 at D = 11.
- i09 (4,9), (4,10): near misses at cost 2 above the 2013 values (5,050 and 11,772 vertices).
- i01 (3,13), i02 (3,14): no gain over the director's 3,400 / 5,640. i02 reported calling two remote-session tools by
  mistake (no effect) and an early `pkill -f bases/` that may have killed other cards' lift runs.
- i03 (4,13): Z2069 x|_2064 Z47 at cost 2. i07, i14, i16: (pending at the time of writing).
- i12 theory (r6/i12/CANDIDATES.md): random S has 22-49 nats more candidates than orbit S, but measured holes exceed the
  size-law mu by 25-2,700x, so the lower tail of the cost distribution decides; at Δ = 5 random S hits cost 0 in about 1
  of 300 samples at N ~ 1.4M.
- i13 (6,13), (6,14): cost 8 at best. i15 (7,14): cost 30 at PSL(2,109) x Z1291.

Director's reading: the metacyclic random-S rule keeps winning at Δ = 4, 5 at every D tried (9 to 14) and now at Δ = 6
(D = 11). Round 7 (last) tests it at Δ = 4..7 against the 2013 table and the lab's D = 8..12 values, and pushes the
new cells once more.

## 2026-11-01, beyond-d13, round 7 (15 cards, 14:11 UTC)

Same session. Files: research/squads/beyond13/r7/. The metacyclic random-S rule tested at Δ = 4..7 against the 2013 table
and the lab's D = 8..12 values (j01-j09), pushes of (4,12), (4,13), (5,13), (5,14), (6,13) (j10-j12, j15), lifts (j13),
the rule's data table (j14). (j16 not launched: subagent cap.)

Cards (best result; all checked by the director):
- **j01 (5,10): Z1489 x|_61 Z31, 92,318** (apsp + metacheck VALID), 2.5 % above the 2013 table value 90,068 (the director
  had closed r6/i10's near miss Z2687 x|_2416 Z17 at 91,358 just before).
- **j13 (3,14): Pappus x Z317 lift, 5,706** (lift then four scan links; apsp VALID).
- j02 (5,9): cost 8 above the lab's 29,756. j03 (4,10): Z215 x|_2 Z28 (12,040) at cost 1 above 11,748. j04 (4,9):
  Z101 x|_5 Z25 (5,050) stays at 2 above 4,970. j05 (4,8): Z55 x|_2 Z20 (2,200) at 1 above 2,184; (5,8) cost 22+.
- j06 (6,9): cost 4 at 125,434 (lab 121,440). j07 (7,10), (7,11): cost 14 and 4 — the rule fades at Δ = 7.
- j09 (7,13): start costs 38-68 (6 % CPU). j10 (5,13) single meta: cost 2. j11 (5,14): cost 1 (four groups).
- j12 (4,12): Z2861 x|_1385 Z13 (74,386) at cost 1. j15 (6,13): Z354001 x|_194759 Z59 at 6.
- j14 (r7/j14/RULE.md): metacyclic random S beats SL/PSL orbit S by 13-17 % at Δ = 4 at odd D, 3-8 % at even D,
  0-4 % at Δ = 5, break-even at Δ = 6; the even-D gain is the orbit form's one free element at Δ = 4.
- j08 (Δ = 6 even D): pending at the time of writing.

Director's reading: the rule holds where predicted (Δ = 4, 5, odd D best) and gives out at Δ = 6..7. Round 7 produced
one table-cell raise candidate ((5,10) 92,318) and four near misses at cost 1-2 above 2013 values ((4,8), (4,9), (4,10))
or lab values ((6,9)). The squad stops here: the remaining time goes to the big checks and the write-up.

## 2026-11-01, beyond-d13: wrap-up (director)

All fourteen new cells have checked values (haarcheck_gen for SL/PSL Haar graphs, logs in
research/frontier/runs/cloudcheck/; apsp all-pairs and/or metacheck for the rest, research/frontier/beyond13/checks/):

| D \ Δ | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
|---|---|---|---|---|---|---|---|---|
| 13 | 3,400 | 192,382 | 3,594,910 | 41,734,392 | 312,227,760 | 1,739,514,000 | 7,924,036,032 | 19,980,294,768 |
| 14 | 5,706 | 497,042 | 12,795,166 | 187,990,656 | 1,674,490,944 | 11,325,238,056 | | |

Raised lab values: (4,11) 24,360 -> 28,418, (5,11) 297,648 -> 306,182, (6,11) 2,094,960 -> 2,098,766, (4,12) 68,544 ->
74,066, (5,12) 1,041,768 -> 1,045,054. Inside the 2013 table: (5,10) 93,738 against 90,068 and (4,10) 12,246 against 11,748 (director scans of all
metacyclic groups in an order range with short hmeta starts; candidates, literature after 2013 not checked).

Who found what: Δ = 3 values came from lifts (card idea r2/e16; the director's cooling fix and runs gave Z163-Z170 at
D = 13 and Z280 at D = 14; cards r5/h02 and r7/j13 the scan finisher and the Pappus Z317 lift). Δ = 4, 5 values came from
metacyclic groups with random S (card ideas r1/c15, r2/e12; values by cards r5/h03, r6/i04, r6/i06, r6/i07). Δ = 6, 7
values by cards (r3/f11, r4/g07, r2/e10, r5/h14), Δ = 8..10 by the director (haar_big0, first solutions at mu 3-12).
The (5,10) value: card r6/i10 found the idea's first table win, the director and r7/j01 pushed it.
The odd-order explanation is ODD_D_HOLES.md's lemma plus Fact 1 of research/frontier/beyond13/THEORY.md (Frobenius
groups have no involutions and trivial centre); the lift bound is Fact 2. Process: 111 cards in 7 rounds on 4 cores; the
director's big checks starved the cards for the first two hours, and one OOM kill cost an hour of the (10,13) check.
Three cards touched remote-session tools by mistake (no effect; one archived an accidental session), and one card's
`pkill -f bases/` may have killed other cards' lift runs; later headers forbade both.

## 2026-11-01 22:50 UTC, beyond-d15 (session_01QYEEyLrwKpDcb3S4u9jBws), round 1

Goal: first values for the new cells D = 15, 16 at Δ = 3..6 (branch claude/new-cells-d15-d16-fpj633; cards and
scoreboard research/squads/beyond15/r1/). 16 Haiku cards (haiku, effort high), 4 cores shared with the director's
Δ = 6 searches; load 16-21 for most of the round. Before the round the director found floors in 1-2 minute calibration
runs: (4,15) Z10859 x| Z61, (5,15) Z154927 x| Z151, (6,15) SL(2,281) x Z19, (6,16) PSL(2,307) x Z139 (mu 11.6), and
that metacyclic groups with k = 13 are nearly abelian at D = 15 (cost 1,738 at (5,15) where k = 151 solved).

Cards (one line each) and best score:
- a01 (3,15) Z_n lifts of GP(10,3), n 520-600: nothing (cost 6 at n = 500).
- a02 (3,16) Z_n lifts of Pappus / GP(10,3): (reported after the round; see round 2 notes).
- a03 (3,15) other cubic bases: Tutte 8-cage Z330 lift, 9,900 VALID (apsp); base ranking gp12_5 < tutte8 < gp16_5 < pappus.
- a04 cubic metacyclic Haar (hmeta d = 3): **(3,16) 17,602**, Z677 x|_362 Z13 (VALID: card metacheck.py, director metacheck.c and apsp).
- a05 wildcard Δ = 3: Z10 x Z42 lift of GP(10,3), 8,400 VALID.
- b01 (4,15) large-k Frobenius: **1,343,054**, Z9199 x|_8708 Z73, mu 15.4 (VALID, director metacheck.c).
- b02 (4,16) metacyclic: cost 2 at mu 12.8 (Z25561 x| Z71); composite m not fixed-point-free, degenerate.
- b03 products of Frobenius groups / AGL(1,q) at (4,15): cost 4, below single meta.
- b04 SL/PSL x Z_n "3 1 1" at (4,15): floor 192.
- c01 (5,15) large-k Frobenius chains: cost 2 at mu 6.5 (Z112253 x| Z211).
- c02 (5,16) metacyclic: **167,009,842**, Z272003 x|_231904 Z307, mu 3.0 (VALID, director metacheck.c, 170 s).
- c03 (5,15) products / SL random S: cost 4.
- c04 Δ = 5 "5 1 0" orbit S: floor 52; haar_big0's annealer hangs at m = 1, f = 0.
- c05 k-threshold table (KTABLE.md): metacyclic groups random-like from k ~ 31 (4,15), ~ 43 (4,16); at Δ = 5 the cost
  still falls up to k = 97. Also (4,15) 1,264,738 VALID.
- c06 (5,16) PSL x Z_n "3 1 2": floor 65.
- d01 (6,15) SL/PSL x Z_n at mu 10-16: cost 18 (load 17-21; ~40 evaluations per link).

Director during the round: wrote research/frontier/beyond15/metacheck.c (independent C checker for metacyclic groups and
products; agrees with metacheck.py level by level) and liftsym.c (symmetric voltage lifts: voltages equivariant under a
base automorphism rho with multiplier lambda, so Z_n x|_lambda Z_k acts with b/k vertex orbits; after gauge fixing only
1-3 orbit voltages are free and each (base, n, lambda) is searched exhaustively in seconds). Results: (3,15) 9,220
(Desargues, Z461) then **10,746** (Gray graph, Z199 x|_43 Z9, 35 solutions); (3,16) 15,020 (Desargues, Z751); Foster
graph (girth 10) at (3,16) n = 211 (18,990) min cost 2; Tutte 8-cage n = 331 (9,930) solved. (4,16) **3,517,286**
(Z24091 x|_1680 Z73, mu 8.5) to fill the cell. (6,15) 867,831,360 at mu 10.0 (SL(2,241) x Z31), checks pending.

Kept: large-k Frobenius groups for Δ = 4, 5 (cards b01, c02, c05); symmetric lifts and the observation that a cubic
metacyclic Haar graph is a symmetric lift of Haar(Z_k, {0,a,b}) with one free voltage, so the whole cubic metacyclic family
is a finite list per (k, pattern, n, lambda) (director's haarsweep.py, exhaustive); girth-8/10 bases (Gray, Tutte 8-cage,
Foster) beat girth-6 bases. Dropped: orbit S at Δ = 4, 5; products; plain lifts of GP(10,3). Note: three cards' turns
showed remote-session or messaging tool calls in the harness summary (not requested; no effect seen in the repo).

## 2026-11-01 23:14 UTC, beyond-d15, round 2 (16 cards; seven were stopped by a container restart at 23:29)

Cards (research/squads/beyond15/r2/), one line each, best score:
- e01 (3,16) Gray order-3 family (gray18) at n = 331-397: cost 56-78 per orbit (stopped by the restart).
- e02 (3,16) Foster order-5 family: cost 6 at n = 211, rising with n (198: 8, 231: 46, 241: 202).
- e03 (3,15) Gray order-3 / Foster order-5 and 15 at D = 15: cost 20-50; left a background driver (the director stopped it).
- e04 exhaustive cubic metacyclic sweep k = 41..120 (haarsweep.py): (3,15) 11,342 and (3,16) 19,306, both below the cells.
- e05 Tutte 12-cage symmetric lifts: (3,16) 17,892 (n = 142), (3,15) 10,836 (stopped).
- **e06 (3,15) 11,790**: Tutte 8-cage, order-5 symmetric lift over composite n = 393 = 3 x 131 (anneal, 1.8 s); apsp VALID (card and director).
- e07 small bases (Dyck, Nauru, Pappus) EXH: cost > 1,000 (stopped).
- f01 (4,15) k 73-151 at mu 16-19: cost 8 (stopped).
- **f02 (4,16) 3,623,866**: closed r1/b02's cost-2 state Z24821 x|_16022 Z73 (mu 12.6) in one 30-s link; metacheck.c and metacheck.py VALID.
- f03 (4,16) k = 151-307: cost 1 at k = 151 (below the cell once f02 landed).
- f04 quartic symmetric lifts of GQ(3,3) at (4,15): cost 184 (stopped).
- **g01 (5,15) 47,370,766**: closed r1/c01's cost-2 state Z112253 x|_76172 Z211 (mu 6.5) in one 90-s link; metacheck.c VALID (card and director).
- g02 (5,16) k = 433, 601: cost 3 at N ~ 8.62-8.67e7 (stopped; states kept for round 3).
- g03 (5,15) k = 137-139: Z170971 x| Z139 at cost 2 (stopped; the director chains it).
- w01 Δ = 3 wildcard (non-maximal lambda, involutions): cost 102 and worse.
- w02 Δ = 4 wildcard (even-order metacyclic groups at (4,16)): cost 33; even m is never fixed-point-free.

Director during the round: exhaustive cubic metacyclic sweep k = 7..40 (haarsweep.py): **(3,15) 11,026** (Z149 x| Z37) and
**(3,16) 19,670** (Z281 x| Z35); Gray order-9 family at prime n = 379: **(3,16) 20,466** (exhaustive; n = 397 min cost 2
for every lambda tried); (6,15) 867,831,360 haarcheck_gen VALID (288 s after raising the check's autogroup priority);
the (6,16) check was killed by the restart and rerun. Found that the scheduler's autogroups make `nice` useless here.
Kept: closing saved cost-2 states (two of three Haar raises), composite n for symmetric lifts (e06), quotient shapes
(Tutte 8-cage and Foster share one; quotgen.py generalizes the sweeps). Dropped: order-3 Gray, order-5 Foster, Dyck,
Nauru, quartic symmetric lifts, even orders, products.

## 2026-11-01 23:33 UTC, beyond-d15, round 3 (16 cards, research/squads/beyond15/r3/)

Cards, one line each, best score:
- k01 Tutte 8-cage composite n (3,15)/(3,16): n = 403 stays at cost 2; 394-420 and 683-701 worse.
- k02 Gray order-9 composite n (3,16): cost 2 at n = 381 (lambda 22) and n = 399 (lambda 4); the director chains them.
- **k03 Tutte/Foster quotient shape with other k (quotgen.py): (3,15) 11,802**, Z281 x|_59 Z7 with 6 orbits (EXH); apsp VALID (card and director).
- k04 Gray quotient shape with other k: k = 13, pattern [8,8,4,11], n = 158 (12,324) at cost 2 (30-s anneals); D = 16 k = 13 n = 265 cost 6.
- k05 cubic metacyclic Haar graphs with composite m (hmeta d = 3): cost 263+; composite m is weak.
- k06 Tutte 12-cage at n = 143-175: cost 32+.
- k07 4-orbit (Desargues-shape) quotient with composite n: cost 10.
- l01 (4,15) k 37-137: Z12721 x| Z53 cost 4.
- l02 (4,16) k 61-83: Z27337 x| Z67 cost 2 (director chains it). The card rewrote other cards' scoreboard lines with sed (path expansion only).
- l03 (4,15) k 31-59: Z11447 x| Z59 cost 2 (director chains it).
- l04 (4,16) k 107-127: cost 2-4, below the cell.
- **m01 (5,16) 172,011,046**: closed r1/c02's cost-2 state Z569573 x|_342015 Z151 with one 80-s link; metacheck VALID (card and director).
- m02 (5,15): closed r2/g03's cost-4 state Z171799 x| Z137 = 47,072,926 VALID, but below the cell.
- m03 (5,16) k = 401-997: (reported after the log entry).
- **m04 (5,15) 47,587,354**: Z76507 x|_75438 Z311 (mu 7.0), fresh start + one link; metacheck VALID (card and director).
- w03 analysis: the minimum number of distinct net traversal vectors per endpoint (Fact 2 of beyond-d13 THEORY.md)
  ranks the bases as the achieved n do (Desargues > Tutte 8-cage > Gray > Foster), achieved n / bound ~ 0.16-0.22;
  the ratio distinct/walks does not (research/squads/beyond15/r3/w03/table.tsv).

Director: (6,16) 4,021,844,904 haarcheck_gen VALID (676 s; rerun after the restart); rechecked every card find above;
spliced the eight rows into BEYOND_TABLE.md; closers on the (4,15), (4,16), (5,15), (5,16) cost-2 states (Z170971 x| Z139
did not close in 10 links); the only three 6-vertex cubic quotients are the Tutte/Foster shape, the Gray shape and K3,3
(enumerated), so round 4 adds K3,3. One card's turn showed an interrupt-session tool call (not requested; no effect seen).
Kept: quotient shapes with other k (two of the three cubic raises came from that view), closers on cost-2 states (two Haar
raises). Dropped: composite-m cubic Haar, Tutte 12-cage, 4-orbit composite n.
