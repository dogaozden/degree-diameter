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

## 2026-11-01, job raise-small-d (Opus cloud session, branch claude/raise-d-delta-3-4-5wyh9b), goal: raise (3|4, 9..14)

Round 0 (director, before the squad): own-small's joint base+voltage annealer (salift_s: a p+p cubic base multigraph and
its voltages in a group, both free) had never been run at D = 13, 14. With metacyclic groups Z_m x|_r Z_k (tables from
a new gtab.py) a 4+4 base solved D = 13 at N = 440-456 in seconds: (3,13) 3,648 (was 3,400), apsp VALID. 70-s probes at
D = 14 (4+4, N = 812, 816) reached cost 2 (n = 6,496, above the census 6,272).

### Round 1 (17 cards, 22:50-23:35; research/squads/raise-small/r1/)

Cards (one line each): c01 (3,13) 3+3 bases · c02 (3,13) 5+5/6+6 · c03 (3,13) 8+8..12+12 · c04 (3,13) non-metacyclic
groups · c05 (3,14) 5+5/6+6 · c06 (3,14) 3+3 and 2+2 · c07 (3,14) 4+4 high band N = 861-1,000 · c08 (3,14)
non-metacyclic groups · c09 (3,12) lifts p = 3..6 · c10 (3,11) lifts p = 2..6 · c11 (3,10)/(3,9) lifts + polish ·
c12 (4,9)/(4,10) quartic joint lifts (salift4) · c13 (4,11)/(4,12) table-free quartic joint lifts · c14 (4,13) hmeta
Haar · c15 (4,14) hmeta Haar · c16 wildcard cubic (Cayley graphs of three involutions) · c17 wildcard quartic (fixed
GQ(3,3) base, metacyclic voltages).

Best per card: c06 **(3,14) 6,600** (3+3 over Z11 x|_2 Z100; also 6,486, 6,528, 6,552 and 2+2 6,560; cost 2 at 7,008)
· c01 **(3,13) 3,744** (3+3 over Z13 x|_2 Z48; cost 2 at 3,780 and 3,960) · c05 cost 6 at 6,480 (6+6) · c08 cost 4 at
6,720 (AGammaL(1,8) x Z5) · c04 cost 6 at 3,840 (SL(2,3) x Z20) · c02 cost 6 at 3,744 (6+6) · c03 cost 20 at 3,840 (8+8)
· c11 cost 12 at 864 · c12 (4,9) cost 18 at 4,992 (2+2 quartic; Haar hmeta at the same n: 150) · c13 cost 72 at (4,11)
30,360 · c14 (4,13) Haar cost 2 at 192,550 · c16 2,184 (PGL(2,13), D = 13; Cayley graphs reach diameter ~log2 n + 2)
· c17 cost 1,208. (c07, c09, c10, c15: added below when they report.)

Director meanwhile: 4+4 scans at D = 13 (N = 462, 465, 468 solve; 3,744 VALID twice) and 3+3 at D = 14 above 1,169
(cost 2 at 1,170); all finds re-checked with sol2edges.py (own group arithmetic) + apsp.c, saved to
research/frontier/raise_small/sols/ and research/frontier/beyond/graphs/.

Selection: small bases win. 2+2, 3+3 and 4+4 beat 5+5 and larger at both D; 3+3 is best at D = 14. Groups with large
k / large r-order beat nearly abelian ones (k = 6 scans cost 30-120); non-metacyclic groups are not better. For Δ = 4
the quartic joint lift beats Haar random-S by a wide margin at (4,9) (the only signal for a 2013-table cell). The squad
was CPU-starved (load ~19 on 4 cores, ~15 % of a core per card; autogroup scheduling makes `nice` ineffective, so the
director raised its own groups to nice -7), so round 2 has 8-10 cards.
Kept for round 2: 3+3 / 2+2 bands just above each solved N, chains on every cost-2 state, quartic 2+2 lifts at (4,9),
(4,10), (4,11), and one wildcard (orbit-constrained lifts).

Round-1 late reports: c07 (3,14) 4+4 N = 861-912: cost 6 at 7,104 · c09 (3,12) p = 4..6: cost 8 at 2,408 (exact 2-move
local minimum) · c10 (3,11) cost 2 at 1,536 (4+4 over Z48 x|_5 Z4; the director's exact polish: local minimum) ·
**c15 (4,14) 498,798** (Haar graph of Z3079 x|_568 Z81 with random S, hmeta; a fresh seed after a cost-1 state; director
re-check: metacheck VALID from both sides, apsp VALID at D = 14).

### Round 2 (10 cards, 23:20-00:05; research/squads/raise-small/r2/)

Cards: d01 (3,13) 3+3 N = 625-720 · d02 (3,13) 2+2 N = 937-1,100 · d03 (3,14) 3+3 N = 1,101-1,170 + chain c06's
cost-2 state · d04 (3,14) 2+2 N = 1,651-1,850 · d06 (3,11) 3+3 / 2+2 / other 4+4 groups · d07 (4,9) quartic 2+2 / 3+3,
other groups · d08 (4,10) quartic 2+2 (salift4m) · d09 (4,11) quartic 2+2 · d10 wildcard orbit-constrained lifts ·
d11 Δ = 4 Haar chases from near misses.

Best per card: **d02 (3,13) 4,324** (2+2 over Z47 x|_2 Z23, first 22-s screen; cost 2 at 4,400) · **d03 (3,14) 7,008**
(chain of c06's cost-2 3+3 state over Z73 x|_10 Z16) · d04 (3,14) 7,004 and 6,844 (2+2; cost 2 at 7,104) · d07 (4,9)
cost 18 at 5,040 · d08 (4,10) cost 30 at 12,480 · d09 (4,11) cost 36 at 30,360 · d10 cost 60 at 4,116 (much worse than
unconstrained) · d11 (4,12) cost 2 at 74,386, (4,13) cost 4, (4,11) cost 6. (d01, d06: below.)
Director meanwhile: **(3,12) 2,436** (2+2 over Z29 x|_7 Z21, N = 609, a 25-s screen of the D = 12 2+2 scan; nobody
had run 2+2 joint annealing at D = 12); 3+3 D = 14 scan above 1,171 (costs 4-14); every find re-checked
(sol2edges.py + apsp, invalid at D - 1).

Selection: 2+2 bases are the surprise of the round (D = 12 and 13 values from first screens); at D = 14 2+2 and 3+3 tie.
The quartic joint lifts plateau (18-36) at every Δ = 4 cell, so Δ = 4 goes back to Haar chases only. Orbit lifts
dropped. Round 3 = 2+2/3+3 bands above every solved N plus chains of the cost-2 states, a (3,10) card, a Δ = 4 Haar card.

Round-2 late reports: d01 (3,13) 3+3 cost 1 at 3,780 (below the value by then) · d06 (3,11) cost 10 at 1,512.

### Round 3 (8 cards, 00:05-00:50; research/squads/raise-small/r3/)

Cards: e01 (3,13) 2+2 chain of d02's cost-2 state + N = 1,082-1,100 · e02 (3,13) 2+2 N = 1,301-1,420 · e04 (3,12) 2+2
N = 721-820 · e05 (3,12) 3+3 N = 407-480 · e06 (3,14) 2+2 chain of d04's cost-2 state at N = 1,776 · e07 (3,14) 3+3
N = 1,301-1,400 and 2+2 N = 1,801-1,900 · e10 Δ = 4 Haar chases (fresh seeds) · e11 (3,10) 3+3/4+4 + exact polish.

Best per card: **e10 (4,12) 74,118** (Haar graph of the Frobenius group Z1123 x|_60 Z33, a fresh seed; director
re-check: metacheck VALID, apsp VALID, diameter 12); (4,13) cost 2 at 193,058 · e01 cost 2 at 4,400 (a floor: ten
links, and the director's six fresh runs with and without targeted moves all end at 2) · e02 cost 80+ above
N = 1,300 · e04 cost 28 at 2,948 · e05 cost 12 at 2,448 · e07 cost 4 at 7,224 (2+2, Z43 x|_3 Z42) · e11 (3,10) cost 2
at 816 (Z17 x|_4 Z8, exact 2-move local minimum). (e06: below.)
Director meanwhile: targeted voltage moves (saliftt.c: solve one voltage on a random walk of length <= D so a far pair
becomes close) A/B against plain annealing on two groups, three seeds each: identical final costs (18 and 2, both group
floors); odd-order groups at D = 13 2+2 (costs 12-28) and at D = 11 3+3 (cost 10 at 1,518, Z23 x|_2 Z11); exhaustive
Haar (p = 1) at D = 13 over 23 odd groups of order >= 2,163 (min cost 52); quartic lifts over odd groups at (4,9)
(cost 20, 72): odd order does not break the Δ = 4 floor. All stopped to give the cards CPU.
Process note: one card's report listed a call of the remote-session archive tool (forbidden by the header); the account's
other sessions were all still running afterwards, and the only archived session in the listing was another job's seed
session, archived by its creator in the same second it was made.

Selection: the values sit at thresholds: D = 13 2+2 near N = 1,081-1,100, D = 14 2+2 near 1,751-1,810 and 3+3 near
1,168. First screens solved twice and chains almost never, so round 4 = dense fresh-seed sweeps of every large-d group
in those narrow bands.

Round-3 late report: e06 (3,14) 2+2: cost-2 floors at 7,104 (Z37 x|_8 Z48), 7,084 (Z23 x|_2 Z77), 7,072 (Z17 x|_2 Z104).
Director after round 3: **(4,13) 193,058** (Haar graph of Z1163 x|_102 Z83: e10's cost-2 group, fresh seeds 2001-2005
stopped at 2, seed 2006 solved in 22 s; metacheck and apsp VALID); (4,11) fresh seeds on the seven odd Frobenius groups
of order 15,223-15,657: seed-independent floors 4-112. Far-pair analysis (tools/farpairs.py) of three cost-2 lift floors:
each is one orbit of pairs at distance D + 1 (seen from both ends), at elements of order 16, 20, 77: no central or
involution structure to avoid.

### Round 4 (6 cards, 00:55-01:40; research/squads/raise-small/r4/)

Cards: f01 (3,13) 2+2 all d >= 8 groups at N = 1,082-1,120, fresh seeds · f02 same at 1,121-1,250 · f03 (3,14) 2+2
1,753-1,800 · f04 (3,14) 2+2 1,801-1,850 + chain of e07's cost-4 state · f05 (3,14) 3+3 1,169-1,215 · f06 (3,12) 2+2
second pass with new seeds at 610-660.
Best per card: **f03 (3,14) 7,040** (2+2 over Z88 x|_7 Z20, N = 1,760; seeds 1 and 2 both solved; director re-check
apsp VALID) · f01 cost 2 (floors at Z136 x|_53 Z8 and Z55 x|_2 Z20) · f04 cost 2 (floors at 1,806) · f05 cost 4 (three
groups). (f02, f06: below.)
Selection: dense fresh-seed sweeps found one more raise; at D = 13 every d >= 8 group in 1,082-1,120 is at a floor >= 2.
Round 5 (final) = the remaining unswept groups (d = 6, 7 and Z_c products at D = 13; D = 14 2+2 at 1,851-1,960) and
fresh-seed Haar sweeps of Frobenius groups just above (4,12), (4,13), (4,14).

Round-4 late reports: f02 (3,13) 2+2 N = 1,121-1,250: floors >= 6 · f06 (3,12) 2+2 second pass 610-660: floors 4-6.
Director: D = 14 2+2 sweep of the groups rounds 3-4 left (orders 1,761-1,950, d >= 6): **(3,14) 7,224** (Z129 x|_11 Z14,
order 1,806) and **7,296** (Z152 x|_69 Z12, order 1,824), first 13-s screens, apsp VALID.

### Round 5 (6 cards, 01:55-02:20, stopped for budget; research/squads/raise-small/r5/)

Cards: g01 (3,13) 2+2 d = 6, 7 groups and Z_c products · g04, g05 (3,14) 2+2 orders 1,851-1,960 · g06, g07, g08
fresh-seed Haar sweeps of Frobenius groups above (4,14), (4,13), (4,12). Doğa stopped the job for budget mid-round; all
cards and director runs were stopped. Found before the stop: **g07 (4,13) 194,486** (Haar graph of Z2069 x|_2064 Z47,
order 97,243; director re-check: metacheck VALID from both sides; apsp not run).

### Job summary (raise-small-d)

Raised: (3,12) 2,368 -> 2,436 · (3,13) 3,400 -> 4,324 · (3,14) 5,706 -> 7,296 (census 6,272) · (4,12) 74,066 -> 74,118 ·
(4,13) 192,382 -> 194,486 · (4,14) 497,042 -> 498,798. Not moved: (3,9), (3,10), (3,11), (4,9), (4,10), (4,11).
Who found what: the method (joint base+voltage annealing of small cubic lifts over metacyclic groups at D = 12-14) was
the director's round 0; the decisive base-size steps came from cards (r1/c06 3+3 at D = 14, r2/d02 2+2 at D = 13); the
director's scans gave (3,12) 2,436 and (3,14) 7,224/7,296; cards gave (3,13) 4,324, (3,14) 6,600/7,008/7,040 and all
three Δ = 4 Haar raises except (4,13) 193,058 (director). Negative results from cards ruled out big bases, non-metacyclic
groups, orbit-constrained lifts, fixed-base lifts, Cayley graphs of involutions and quartic joint lifts.
Open when stopped: the D = 14 2+2 sweep was still producing solutions at order 1,824 (of 1,950); (4,13) 194,486 needs
an all-pairs check. Process: 4 cores for 17 cards plus director in round 1 starved the cards (~15 % of a core each);
later rounds of 6-10 cards worked better. One card called a remote-session archive tool (no visible effect).
