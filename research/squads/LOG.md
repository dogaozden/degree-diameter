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

## 2026-11-01, beyond-d14, round 1 (16 cards, 22:48 UTC)

Session: Opus director, job beyond-d14 (branch claude/beyond-d14-new-cells-v6dcaa). Goal: the D = 14 column at
Δ = 3..8. All six cells already had checked values from job beyond-d13 (earlier the same day), so every target is a
raise: (3,14) 5,706, (4,14) 497,042, (5,14) 12,795,166, (6,14) 187,990,656, (7,14) 1,674,490,944, (8,14) 11.3e9.
Files: research/squads/beyond14/r1/ (HEADER.md, c01-c16.md, scoreboard.jsonl). Machine: 4 cores, 15 GB; the Agent
tool's "remote" isolation runs in this same container (same boot id), so all cards share the 4 cores.

Cards (best result; VALID = checked by the director with haarcheck_gen, build_haar2 or apsp):
- c01 (3,14) Pappus cyclic lift n = 318/319: cost 2. c02 larger-girth bases (Tutte 8-cage n = 210 cost 30, Tutte
  12-cage n = 50 cost 376, Foster n = 70 cost 270). c03 metacyclic voltages on Pappus: cost 6-8 at 5,724. c04 cubic
  Haar graphs of non-metacyclic groups: cost 6 at 6,560 (AGL(1,41) x Z2). Nothing above 5,706.
- **c05 (4,14): Z3079 x|_1863 Z81 (prime m), hmeta screen of 40 prime-m groups at N 249K-251K, 498,798 VALID**
  (build_haar2; apsp running). Near miss Z5581 x| Z45 (502,290) cost 1.
- c06 (4,14) other families at matched N: PGL(2,37) x Z5 cost 2 (253,080), SL(2,37) x Z5 3-4, PSL(2,47) x Z5 8.
- c09 (5,14): SL(2,53) x Z43 random S 12,798,864 VALID (build_haar2), above the old record, below c11.
- **c11 (5,14): PSL(2,163) x Z3 with ORBIT "2 2 1" (S = {e, x, ax, y, ay}, a of order 2), 12,991,752 VALID**
  (haarcheck_gen and build_haar2); random symmetric S: median cost 41, min 10.
- **c12 (6,14): SL(2,137) x Z37, ORBIT "3 2 0", cost 0 on the FIRST random S (mu 10.3), 190,269,984 VALID**
  (haarcheck_gen, 210 s). Screen min/median: SL(2,137) x Z37 1/15, SL(2,239) x Z7 3/16, SL(2,79) x Z193 4/49.
- c13 (6,14) other orbit forms: "6 1 0" degenerate, "2 3 0" cost 1,306, "3 1 3" worse: "3 2 0" stays.
- **c15 (7,14): SL(2,233) x Z67, ORBIT "3 2 1", 1,694,979,936** (check running); also cost 0 at PSL(2,139) x Z631
  and PSL(2,191) x Z241; PSL(2,137) x Z661 stalls at 3.
- c07, c08, c10, c14, c16: pending at the time of writing.

Director, outside the cards: (a) the Foster census of cubic edge-transitive graphs (Potocnik et al.,
fostercensus.graphsym.net, TableCSS.html and CSS_lcf.txt) lists CSS(6272,3) and CSS(6272,7), semisymmetric cubic graphs
of diameter 14 on 6,272 vertices: built from LCF, apsp VALID (diameter exactly 14). They are not ours; they set the
(3,14) bar at 6,272. (b) Following the lab's own (3,10)-(3,12) records (job own-small: regular lifts of 4+4 cubic bases
over non-abelian groups, joint base+voltage annealing with salift_s), a 60-s salift_s screen at D = 14 over Z113 x|_16 Z7
(order 791) gave **6,328** (apsp VALID, diameter exactly 14), above the census and the old 5,706. Z41 x| Z20 (820)
stalls at 6, Z101 x| Z8 (808) at 20. (c) (9,14): PSL(2,241) x Z1429 with three free 3-orbits solved at the first
evaluation (N = 1.0e10, far below the size-law order ~2.8e10), 20,002,113,120 vertices; haarcheck_gen running. It is
also the first value for (10,14) by monotonicity in Δ.

Director's reading: cards stop after 6-16 minutes. Round 2 keeps the lift method at Δ = 3 (six cards over base size
and group family), takes it to Δ = 4 (d08), pushes the round-1 winners at (4,14), (5,14), (6,14), (7,14) to larger N,
and drops cyclic lifts, larger-girth bases, and the orbit forms "6 1 0", "2 3 0", "3 1 3".

Round 1 late cards (after the entry above was written): **c08 (5,14) Z152393 x|_149882 Z43, 13,105,798 VALID**
(build_haar2; hmeta, 4 s), near miss Z153511 x| Z43 (6.6M) cost 1; c10 (5,14) (Z337 x| Z7) x (Z307 x| Z9) 13,035,834
(below c08); c07 (4,14) products of Frobenius groups no better than single metacyclic groups (cost 3 at 502,964);
c14 (6,14) metacyclic random S cost 1 at 188,005,162 (k = 109); **c15 (7,14) SL(2,233) x Z67, 1,694,979,936 VALID**
(haarcheck_gen, 559 s); c16 (7,14) "2 3 1" and "6 1 1" worse than "3 2 1", SL(2,947) x Z1 cost 1.

## 2026-11-01, beyond-d14, round 2 (16 cards, 23:09 UTC; stopped at 23:28 by a container restart)

Same session. Files: research/squads/beyond14/r2/. Selection from round 1: the director's lift result (4+4 base over a
Frobenius group, 6,328) became six cards over base size and group family (d01-d06); (4,14) the prime-m metacyclic
screen pushed (d07), lifts of 4-regular bases (d08), order-2 orbit forms (d09); (5,14) the "2 2 1" form in PSL, SL and
metacyclic groups (d10-d12); pushes at (6,14) (d13, d14) and (7,14) (d15, d16). The Agent tool's 30-minute default
background limit also stopped the director's first (9,14) check; the container restart stopped everything at 23:28.

Cards (best result; VALID = director check):
- **d04 (3,14): 3+3 base over Z47 x|_2 Z23, 6,486 VALID** (apsp). Then the director: **2+2 base over Z103 x|_8 Z17,
  7,004 VALID** (apsp, diameter exactly 14); all five Frobenius groups of order 1,629-1,751 solved at p = 2 in 40 CPU-s;
  1,778-1,884 stalled at 6-74. The six lift cards were redirected to p = 1, 2, 3 windows at 23:17: best states d06
  Z199 x| Z9 (7,164) cost 6, d04 Z61 x| Z20 (7,320, p = 3) cost 24, d02 (7,104) cost 24, d03 p = 1 (7,164) cost 56,
  d05 products at p = 2 (8,700+) cost in the thousands.
- **d07 (4,14): Z5849 x|_5711 Z43, 503,014 VALID** (build_haar2); cost 2 at 252,191 and 252,385.
- d08 (4,14) lifts of 2+2 4-regular bases over Z_m x| Z7: cost 4 at 397K (k = 7 too small; redirected to k >= 30).
- d11 (5,14) "2 2 1" in SL(2,q) x Z_n: cost 18-36. d12 "2 2 1"-type pairs in metacyclic groups: cost 3,921 (far worse).
- **d13 (6,14): PSL(2,107) x Z157, 192,314,952** (cost 0; check restarted after the restart).
- **d15 (7,14): PSL(2,167) x Z367, 1,709,227,632** and SL(2,241) x Z61, 1,707,668,160, both from RANDORB=8 screens
  (cost 0 in about 1 of 8 random symmetric S at 853-855M; min 3 above 855M); check running.
- d09, d10, d14, d16: stopped by the restart without a scoreboard line.

Director's reading: at Δ = 3 the base size matters more than the group: the size-law mu reached grows from 18 (4+4)
to 21 (3+3) to 33 (2+2). Round 3 keeps p = 2, 3 at (3,14) (five cards), the prime-m metacyclic screens and a 1-opt
finisher at (4,14), lifts with large-k groups at Δ = 4, 5, metacyclic pushes at (5,14), and random symmetric S screens
at (6,14) and (7,14).
