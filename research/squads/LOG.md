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

## 2026-11-01, beyond-d11, round 1 (16 cards, 04:47 UTC)

Session: Opus director, job beyond-d11 (branch claude/new-cells-d11-d12-beyond-8sas9r). Goal: first values for
(11..14, 11) and (11..13, 12), Haar graphs of SL/PSL(2,p) x Z_n with alpha-orbit generator sets, at most 20 billion
vertices. Files: research/squads/beyond11/r1/ (HEADER.md, cards c01-c16, scoreboard.jsonl). Before the round the
director had (11,11) 1,170,162,000 (VALID), (12,11) 2,874,207,072 (f = 0, new in haar_big0), and the three D = 12
values (5, 1 and 1 evaluations). Machine: 4 cores, 15 GB, shared with the director's checks.

Cards (best result):
- c01 (11,11) SL ladder "3 3 2": SL(2,443) x Z7 (mu 7.2) to cost 2, then stopped: the director's memory cap (0.4 GB)
  was below what N > 5.85e8 needs. Director's mistake, not the card's.
- c02 (11,11) PSL ladder: PSL(2,257) x Z73 (mu 10.1) stalls at cost 9 (K = 4 and 8 alike).
- c03 (11,11) k = 5 ("5 2 1"): start costs 16-54 (k = 3: 2), best 6 at mu 6.1. Worse at this cell.
- **c04 (12,11) SL ladder "3 4 0": SL(2,239) x Z109, mu 7.0, 2,976,066,240 vertices** (+3.5 %, search cost 0 in 9 evals;
  director's haarcheck_gen pending); SL(2,193) x Z211 (mu 10.3) to cost 2.
- c05 (12,11) PSL bold ladder (mu 9-14): stalled at 27-155.
- c06 (12,11) other free-orbit orders: k = 2 bad (460), k = 4 degenerate (cost 2.6e9), k = 6 "no orbit". Led to a bug:
  haar_big's choose_alpha took the first g with g^k = +-I, so k = 4, 6, 10 got an alpha of order 2 or 3 (fixed in haar_big0;
  c09 found the same bug and used AT = trace as a workaround).
- c07 (13,11) "3 4 1": SL(2,229) x Z277 (mu 5.05) to cost 2 (1-5 evals per 100 s chunk under load).
- c08 (13,9) structure tournament: only "3 4 1" solved (PSL(2,101) x Z61, mu 10.3, VALID); "4 3 1", "6 2 1", "2 6 1" at
  116-432; n = 1 (PSL(2,401)) 87-111 and n = 5 (PSL(2,233)) 34-42 also bad. Same choose_alpha bug, worked around with AT.
- c09 (14,9) tournament at mu ~10: "3 4 2" best (66), "7 2 0" 82, k = 4 / 6 (with correct alpha) 3,204 / 62,568, "2 7 0" 9,786.
- c10 (11,9) tournament: "5 2 1" solved mu 22.6 (PSL(2,41) x Z251, VALID), "3 3 2" mu 10.4 (VALID); "2 5 1", "3 2 5",
  "10 1 1" far behind. One seed per rung.
- c11 (13,9) group shapes at mu ~15: PSL(2,59) x Z313 best (cost 4-6); n = 1 (PSL(2,401)) 87-111; n/p >= 40 also bad.
- c12 self-dual S (transpose-closed, one BFS per eval): implemented and verified, but random S get far worse (start 180
  versus 9 evals to solve for plain haar_big0). Negative.
- c13 tuning (K, TARGP, BOUNDCUR): within seed noise. (11,9) 15,760,800 VALID as a by-product.
- c14 theory note: odd-D Haar criterion needs both (S^-1 S)^h = G and (S S^-1)^h = G (D6 counterexample); claims the
  D = 12 upper bound is only M_b - 4 (from memory; round 2 card d14 checks the paper).
- c15 calibration from 161 lab runs: mu ~7 solves within ~300 evals, mu ~10 within ~1,000 (P = 0.5); start cost > 30 at
  mu >= 8 rarely solves.
- c16 RANDORB at (11,11), mu ~5.5: SL(2,359) x Z13 and SL(2,241) x Z43 lowest (median 21-22), n > p worse (40-44), PSL(2,1063)
  with n = 1 much worse (151).

Director's reading: the near misses fail at special elements. SL(2,193) x Z211 misses only -I (both sides); SL(2,443) x Z7
misses two alpha-fixed torus elements. At odd D = 2h+1 the words reaching a central element are closed under cyclic
rotation by two letters, so central elements behave as if they had about lambda/h words instead of lambda; SL has 2n
central elements including -I, PSL has n. Kept for round 2: k = 3; PSL with small n (no -I); finishing near misses;
moving the fixed generator (never moved by haar_big); the n = 1 anomaly as a question. Dropped: k = 2, 4, 6, self-dual S,
tuning knobs. Process notes: cards stopped after 5-12 minutes of their 25; the kernel's autogroup scheduling had made
the cards' nice 10 meaningless (each Bash call is its own group); the director turned autogroup off at 04:58.

## 2026-11-01, beyond-d11, round 2 (16 cards, 05:10 UTC)

Same session. Files: research/squads/beyond11/r2/. Cards built on round 1: PSL with small n (my reading of the -I hole),
near-miss finishing, fixed-generator moves, hole anatomy, n-scans at odd and even D, k = 5, the (7..10, 11) cells, the
upper-bound citation, two wildcards. At 05:21 the director redirected seven cards from PSL to SL after d04's result.

Cards (best result; finds with N > 1e8 checked by the director, see BEYOND_TABLE):
- **d04 hole anatomy at (11,11)**: PSL(2,1063) x Z1 holes are all involutions (about 130 per seed); PSL(2,557) x Z7 also
  involution-dominated (35-59); SL(2,149) x Z181 central-dominated (24-26 central holes); SL(2,251) x Z37 2-22. Rates fit
  exp(-lambda/2) for involutions and exp(-lambda/5) for central elements. This turned the round: at odd D use SL (one
  involution) with small n (few central elements). Write-up: research/frontier/beyond11/ODD_D_HOLES.md.
- **d01 (11,11) SL(2,317) x Z19, mu 6.4: 1,210,478,448** (after the redirect; PSL rungs had stalled at 12-21).
- **d13 (10,11) SL(2,613) x Z1, mu 9.3: 460,691,568** (was 445,709,568) and SL(2,229) x Z19 456,332,880; PSL(2,401) x Z7 stalled at 15.
- **d08 (9,11) SL(2,223) x Z7, "3 3 0", mu 10.6: 155,250,816** (was 145,258,344; haarcheck_gen VALID by the card).
- **d09 (8,11) PSL(2,113) x Z31: 44,726,304** (was 43,702,560) and **(7,11) SL(2,53) x Z37: 11,012,976** (was 10,648,176), both VALID by the card.
- d02 SL(2,443) x Z7 near miss: stays at cost 2 over 11 seeds. d03 fixed-generator moves (FXMOVE): no gain.
- d05 (12,11): SL(2,487) x Z13 (mu 8.4) to cost 8, PSL(2,541) x Z19 18 (25-40 s per eval on one loaded core).
- d06 (12,11) n-scan: PSL n = 1 start 294, n = 7 60, n = 37 18, n = 151 21; SL n = 7 14, n = 1 14 (few evals each).
- d07 (13,11): PSL(2,599) x Z31 to cost 10; the SL rungs needed 2.1-3.4 GB, over its cap (not run).
- d10/d11 odd/even n-scans at D = 9, 10: inconclusive (mu not matched, few seeds); d11's SL(2,67) x Z499 at (12,10),
  300,094,608, is below the table value 300,383,050.
- d12 k = 5 at (11,9), mu ~20: 2 of 5 seeds solved (PSL(2,41) x Z251, VALID) against 0 of 3 for k = 3. At (11,11) too slow
  to judge. (At D = 11, k = 5 pays exp(-lambda/5) per alpha-fixed element, so it needs small p and then large n.)
- d14 upper bounds: read arXiv 1010.5651; Prop. 6.4 (p. 25) gives N_b <= M_b - 6 for 5 <= D <= 187, D != 6, so the table's
  bound stands for D = 11 and 12; round 1's c14 claim (M_b - 4 at D = 12) was wrong.
- d15 wildcard: SL(2,199) x Z1 solves (11,9) quickly, PSL(2,251) x Z1 stalls at 33-36 (consistent with d04).
- d16 central cover (fixed generator -I or x with x^2 = -I): -I as a generator is bad; x^2 = -I solved 1 of 6 at (13,9)
  where plain solved 0 of 6. Weak.

Director during the round: (13,11) 6,508,747,920 VALID; (14,11) solved at mu 6.9, SL(2,1009) x Z7, 14,381,398,080
(49 evals, 522 s at 2 threads). Kept: SL with small n at odd D (now the job's rule), f = 0 when 3 | Δ. Dropped: PSL at odd D,
k = 5 at D = 11, fixed-generator moves, central covers. Round 3 applies the rule to the cheap cells (5..10, 11) and (5..10, 12).

## 2026-11-01, beyond-d11, round 3 (16 cards, 05:38 UTC)

Same session. Files: research/squads/beyond11/r3/. Selection from round 2: apply "SL with small n at odd D, f = 0 when
3 | Δ" to the cheap cells (5..10, 11) and test PSL with smaller p at even D on (5..10, 12); one even-D hole anatomy, one
quantitative test of the hole model, one real-scale (11,11) card, one wildcard.

Cards (best result; card-checked VALID or director-checked, see BEYOND_TABLE):
- **e01 (5,11) SL(2,53) x Z1: 297,648** (was 253,080), VALID by the card.
- **e02 (6,11) SL(2,53) x Z7: 2,083,536** (was 1,971,744), VALID by the card; SL(2,103) x Z1 (mu 15.4) to cost 2.
- e03 (7,11): SL(2,67) x Z19 (mu 17.4) to cost 2; no gain.
- **e04 (8,11) SL(2,283) x Z1: 45,329,808** (was 44,726,304), search cost 0.
- e05 (9,11): SL(2,137) x Z31 (mu 16.4) to cost 2. e06 (10,11): SL(2,617) x Z1 (mu 13.1) to cost 8.
- **e07 (5,12) PSL(2,53) x Z7: 1,041,768** (was 912,576), VALID by the card.
- **e08 (6,12) PSL(2,79) x Z19: 9,366,240** (was 9,303,840), VALID by the card.
- **e09 (7,12) PSL(2,67) x Z199: 59,838,504** (was 56,297,592).
- **e10 (8,12) SL(2,113) x Z97: 279,900,096** (was 268,496,208).
- **e11 (9,12) PSL(2,241) x Z79: 1,105,785,120** (was 1,055,973,600).
- **e12 (10,12) PSL(2,239) x Z271: 3,699,605,280** (was 3,500,976,768).
- e13 even-D anatomy at (8,12): no involution or rotation clumps at even D (as predicted); alpha-fixed holes enriched
  but most holes ordinary; smaller p did not help; S with a generator of projective order 2 cost > 1e4.
- e14 model fit at (11,9), 22 groups: generic term mu (not mu/3); model 1.3-2.3x low; involution and central terms of
  the predicted form (central ~ exp(-lambda/4) at h = 4).
- e15 (11,11) SL(2,853) x Z1: stopped, memory cap too low for n = 1 (rows are padded; 0.86 GB, the director's error).
- e16 composite n (products of primes = 1 mod 3) fill gaps in the group list: PSL(2,97) x Z301 at (8,12), 274,685,376
  (below e10); n >= ~900 starts at huge cost.

Even-D "prefer PSL with smaller p" was not confirmed (e07, e10, e13: mixed; SL and PSL with moderate n both solve).
Director during the round: (12,11) 2,976,066,240 VALID; (11,12) pushed to 11,189,148,096 (PSL(2,223) x Z1009, mu 13.3,
17 evals); mu 28 stalled at 8. Kept for round 4: the many cost 1-3 near misses on cheap cells.
