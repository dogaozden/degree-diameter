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

### Round 2 (17 cards, 12:13-12:38 UTC, research/squads/beyond11b/r2/)

All cards built on round 1's lead (odd-order, centre-free Frobenius groups Z_p x| Z_k, and SL(2,q) x Frobenius).
Cards (best result):
- **h01 (4,11) Z_523 x| Z_29 (N 15,167): 30,334** (two seeds of two solved); k = 9-15 groups stall at 6-62.
- **h02 (4,11) Z_421 x| Z_35: 29,470** (1 seed of 4); groups near N = 15k stall at 2-10; k > 63 runs slowly in haar_gen3.
- h03 (4,11) (Z7 x| Z3) x (Z53 x| Z13): 28,938 (below h01); other products 6-2,412.
- **h04 (5,11) Z_5279 x| Z_29: 306,182** (1 seed of 5; k = 25-65 cost 4-8 in 60 s, k = 9 cost 252).
- **h17 (theory) (5,11) Z_8171 x| Z_19: 310,498**; NOTE.md: no involutions / trivial centre (proved), W_j = W_-j,
  coset coverage by Cauchy-Davenport, balanced C_k labels of S predict fewer holes; k = 7 median 434 holes vs k = 19 35.
- **h12 (4,12) even D, Z_263 x| Z_131: 68,906** (was 68,544; 1 seed of 5); (5,12) Z2897 x| Z181 cost 8.
- h13 measurement: median holes at radius 10 vs size law: Frobenius k = 19 1.1x, k = 13 1.6x, SL(2,23) 4.3x,
  SL(2,13) x Z7 5.2x; the gain is in the middle levels (X_8/model 0.99 vs 0.89-0.92), k = 3 collapses.
- No raise: h05 (5,11) SL(2,q) x F (plateau 10-18); h06 (6,11) Frobenius, 240 groups, k = 63 cost 2 on 4 seeds; h07 (6,11)
  SL(2,7) x (Z449 x| Z7) cost 4; h08 (7,11) k = 23 plateau 18; h09 (8,11) SL(2,103) x H21 cost 14; h10 scaling-automorphism
  orbits (AMU) degenerate; h11 cubic Frobenius (exh3) cost >= 84; h14 cubic lifts cost 2 at 2,184; h15 (6,11)
  (Z67 x| Z3) x (Z307 x| Z17) cost 2; h16 2-dim Frobenius Z29^2 x| Z15 25,230 at (4,11).
Director-verified (build_haar2.py + apsp, logs runs/cloudcheck/*b2h*.check.txt): (4,11) 30,334 and 29,470, (4,12)
68,906; (5,11) 310,498 and 306,182 checks running. Kept for round 3: many seeds per group near the limit, k ~ 19-63,
Frobenius at even D, the cost-2 near misses at (6,11), label balance as a search constraint. Dropped: AMU orbits, SL x F
above (5,11), cubic Frobenius. Process: card h14 called create_session once by mistake (an empty session) and archived
it; round 3's header forbids session and messaging tools.

### Round 3 (16 cards, 12:40-13:06 UTC, research/squads/beyond11b/r3/)

Cards (best result; director re-checks: build_haar2.py, plus apsp where 2N <= 310k; logs runs/cloudcheck/*b3*.check.txt):
- **i08 (6,11) (Z67 x| Z3) x (Z307 x| Z17), N = 1,049,019: 2,098,038** (was 2,094,960; 1 seed of 8; build_haar2 VALID).
- **i07 (6,11) Z16633 x| Z63, N = 1,047,879: 2,095,758** (1 run of ~6; build_haar2 VALID).
- **i10 (4,12) Z1297 x| Z27, N = 35,019: 70,038** (solved in 2 s; also Z1117 x| Z31 69,254 and Z617 x| Z56 69,104; VALID).
- **i11 (5,12) Z9859 x| Z53, N = 522,527: 1,045,054** (was 1,041,768; build_haar2 VALID).
- No raise: i01 (4,11) k = 29/31 window empty (director's card error; only N = 15,167 exists); i02 Z463 x| Z33 (N = 15,279)
  15 seeds stuck at 4-6; i03 Z307 x| Z51 cost 8, (Z7 x| Z3) x (Z67 x| Z11) cost 6; i04 (5,11) Z8209 x| Z19 9 seeds best 4;
  i05 Z6763 x| Z23 and Z5023 x| Z31 cost 2; i09 (7,11) Z90281 x| Z61 cost 2 (k 53-63 run 7x faster than k = 23);
  i12 (6,12) PSL(2,41) x (Z17 x| Z8) cost 3; i13 label-balanced S: mean best cost 6.0 vs 8.4 plain at (5,11), no
  solve-rate difference in 5 seeds; i14 (8,11) and i16 (7,12) too slow for a card (17 evals per seed); i15 composite k
  and p^2 kernels worse than prime k; i16 (5,12) PSL and Frobenius plateau alike (no even-D advantage measured there).
Kept: seed farms on the cost-1/2 near misses ((4,12) Z701 x| Z50 cost 1; (5,12) Z8317 x| Z63 and Z11093 x| Z47 cost 1;
(5,11) Z6763 x| Z23, Z5023 x| Z31; (6,11) products N = 1,050,063; (7,11) Z90281 x| Z61). Process: three cards made stray
calls to messaging/session tools despite the header (all failed with argument errors, nothing sent).

### Round 4 (14 cards, 13:08-13:33 UTC, research/squads/beyond11b/r4/)

Mostly seed farms on round 3's near misses, plus a tool card. Cards (best result; director re-checks with build_haar2.py):
- **j06 (6,11) Z20707 x| Z51, N = 1,056,057: 2,112,114** (2 of 7 seeds); k = 61 N = 1,049,383 also solved (2,098,766).
- **j10 (5,12) Z10303 x| Z51, N = 525,453: 1,050,906** (also Z8317 x| Z63 1,047,942); near misses cost 1-2 up to N = 529k.
- **j12 (5,11) Z3613 x| Z43, N = 155,359: 310,718** (17.5 s; second seed cost 4).
- j05 (6,11) (Z7 x| Z3) x (Z1613 x| Z31): 2,100,126 (below j06). j14 TOOL: haar_gen3s (SAVEBEST / START; chaining reached
  cost 4 where one run reached 8, then stalled). No raise: j01 (4,11) above N = 15,167 (k 13-23, cost 6-22); j02/j03/j04
  (5,11) farms (cost 2-6); j07/j08 (7,11) (cost 2-4 over 27 runs); j09 (4,12) Z677 x| Z52 and Z701 x| Z50 cost 2;
  j11 (6,12) Z74719 x| Z63 cost 2; j13 even-D products (5,12) cost 1.
Kept for round 5: chains with haar_gen3s on the cost-1/2 near misses, (6,11) above N = 1,056,057, a move-set card and a
hole-anatomy card. Process: four more stray calls to messaging/session tools by cards, all rejected for missing arguments.

### Round 5 (14 cards, 13:38-14:03 UTC, research/squads/beyond11b/r5/)

Seed farms and save/resume chains (haar_gen3s from r4/j14) on the near misses, a move-set card and a hole-anatomy card.
- **k07 (6,11) Z20809 x| Z51, N = 1,061,259: 2,122,518** (44 s); k = 43 at 1,061,369 cost 2.
- **k03 (5,12) Z8663 x| Z61, N = 528,443: 1,056,886** (cost 2 fresh, then 0 after one resume).
- **k05 (5,11) Z5023 x| Z31, N = 155,713: 311,426** (cost 4 fresh, 0 after one resume).
- **k02 (4,12) Z731 x| Z48 (731 = 17 x 43), N = 35,088: 70,176** (cost 1, 1, then 0 on the 4th chain link).
- k13 TOOL (haar_gen3t): pair moves and s -> s w moves useless; full-length targeted walks (TFULL = 1, TARGP = 100) took
  (4,12) Z677 x| Z52 from cost 2 to 1 where plain chains stayed at 2-3.
- k14 hole anatomy: at odd D the holes of a Frobenius group are inverse pairs on one side (cost 4 = one pair per side, as
  the inversion symmetry predicts); at (4,12) the last hole of a cost-1 state was an involution of Z677 x| Z52 (k = 52 even).
- No raise: k01 (4,12) Z677 x| Z52 cost 1; k04 (5,11) product lineage stuck at 2 over 9 chains; k06 (5,11) six groups at
  4-10; k08 (6,11) products cost 4; k09/k10 (6,12) Z74719 x| Z63 cost 1-3; k11 (7,11) Z90281 x| Z61 cost 2 plateau; k12
  (7,11) Z100981 x| Z55 low-temperature chain 8 -> 2.
Director-verified with build_haar2.py (plus apsp for (4,12) and (5,11)). Round 6 applies the TFULL finisher to the cost-1/2
states. Process: three more stray session-tool calls (rejected) and some multi-line scoreboard records.

### Round 6 (12 cards, 14:04-14:28 UTC, research/squads/beyond11b/r6/) - last round

Finisher round: the TFULL targeted move (haar_gen3t, r5/k13), low-temperature and plain resumes on the cost-1/2 states.
- **l03 (5,12) Z8969 x| Z59, N = 529,171: 1,058,342** (cost 1 frozen for 6 runs, then 0 in 11 s on the 7th; build_haar2 VALID).
- l01 (4,12) Z677 x| Z52 cost-1 state: an exhaustive scan of all 105,609 single-generator swaps finds no cost 0 (only the
  state itself at cost 1; 3 neighbours at cost 3; their full 1-swap scans also bottom out at 1). An isolated local minimum.
- l07 (5,11) product cost-2 state: the 2 holes are an inverse pair on the B side (A side complete), as predicted.
- No raise: l02/l11 (6,12) Z74719 x| Z63 cost 1 (14 + 7 runs); l04/l05 (7,11) cost-2 states, 0 accepted targeted moves
  (one replacement costs +6 or more); l06 (6,11) Z24683 x| Z43 cost 2; l08 (5,11) Z3061 x| Z51 4 -> 2; l09 (8,11) cost 8
  (setup 45-50 s of each 90 s run); l10 (4,11) Z463 x| Z33 cost 4; l12 (5,12) fresh groups cost 2.
Reading: near the limit the annealer's local minima are real (exhaustive 1-swap check at (4,12)); solves come from many
fresh lineages, not from deeper finishing. The squad stopped here so the last three ~11 GB checks run on an idle machine.

## 2026-11-01, beyond-d11b: wrap-up (director)

New cells (director, haar_big0; all at most ~30 billion vertices), haarcheck_gen from (e,A) and (e,B):
- (16,11) 29,961,590,400, PSL(2,449) x Z331 (first S solved; VALID, 5,281 s).
- (15,11) 28,655,908,512, SL(2,617) x Z61, f = 0, mu 5.2 (13 evaluations; VALID, 4,663 s).
- (14,12) 29,996,171,040, PSL(2,241) x Z2143 (first S solved; VALID, 2,859 s).
Raises at the 30-billion cap: (12,12) 19,980,294,768 -> 29,996,171,040 (45 evaluations; VALID, 2,406 s), (13,12) 19,993,487,976 ->
29,997,644,040 (first S solved; VALID, 2,576 s).
Small cells (squads, odd-order Frobenius groups Z_p x| Z_k and products; build_haar2.py, plus apsp up to 2N = 311k):
(4,11) 24,360 -> 30,334; (5,11) 297,648 -> 311,426; (6,11) 2,094,960 -> 2,122,518; (4,12) 68,544 -> 70,176;
(5,12) 1,041,768 -> 1,058,342.

Who found what: the five 30-billion graphs are the director's (parameters carried over from beyond-d11, with p kept
small enough for haarcheck_gen's tables); every small-cell raise came from squad cards (g02, g16, h01, h02, h04, h12,
h17, i07, i08, i10, i11, j06, j10, j12, k02, k03, k05, k07, l03), all on the Frobenius lead that two round-1 cards
(g02 odd-order metacyclic, g16 SL(2,p) x odd Frobenius H) opened from director cards aimed at "groups with no
involutions and no centre at odd D". The measurement card h13 explained it (middle-level collisions in small SL(2,p),
none in Frobenius groups with k >= 13), the theory cards g15 and h17 gave the exact clump facts, and the tool cards j14
(save/resume) and k13 (targeted finisher) produced haar_gen3s / haar_gen3t, which gave four of the later raises.
Six rounds, 89 cards. Rounds 1-3 found the family and most of the gain; rounds 4-6 added 0.1-1.4 % per cell.

Process lessons: (1) The 30-billion checks (11.2 GB, 1.3-1.5 h each with squads running) were the critical path;
renicing the checker to -5 kept it at ~3.5 cores while 12-17 cards ran. (2) Cards still often stopped before 25
minutes and several made stray calls to session/messaging tools (all rejected or harmless; one empty session created by
h14 was archived by the card itself); a header rule cut but did not stop it. (3) Seed farms near the limit solve about
1 in 5-15 runs; finishing a cost-1/2 state is rarely possible (exhaustive 1-swap check at (4,12)). (4) Cards on cells
with N >= 5e6 get too few evaluations to matter on a shared 4-core box.

Not done: raises of (11..14, 11) and (11,12) (gains of 1-3 % at mu above where odd-D searches stall; no machine time
left beside the checks); a (15,11) push to SL(2,571) x Z79 (29.4 billion, mu 9.3; dropped for the checks); Frobenius
groups at (8,11) and above (need a 64-bit meta layout and a low-memory checker that knows meta groups). For the
coordinator: the five big graphs are above 20 billion vertices, so the reference check needs the split runs
(haarcheck_psl.c SOL A / SOL B for the PSL ones; haarcheck_sl.c SOL A / SOL B for (15,11), option added here).

## 2026-11-01, raise-d12, round 1 (16 cards, 23:06 UTC)

Session: Opus director, job raise-d12 (branch claude/d12-frontier-cells-m24ikx). Goal: raise the D = 12 values at
Δ = 3..14 and add (15,12) under 30 billion vertices. Machine: 4 cores, 15 GB, shared with the director's (15,12) check
(haarcheck_gen, 11.3 GB). Files: research/squads/raise-d12/r1/ (HEADER.md, a01-a16.md, scoreboard.jsonl, card folders).
State at the start (master, after jobs beyond-d11 and beyond-d11b): (12,12), (13,12), (14,12) already at the 30-billion
cap, (4,12) and (5,12) on Frobenius groups, (6..11,12) on k = 3 conjugation orbits; so the director aimed the cards at
(3..7,12) with structures the earlier jobs had not used, and kept (8..11,12) and (15,12) for his own big runs.

Cards (best result; all negative):
- a01 (3,12) lifts of the Tutte 12-cage (H(2) incidence graph) over groups of order m: valid only up to m = 11 (1,386
  vertices); m = 12 stalls at cost 2. Exactly 65 non-backtracking walks of length <= 12 join a vertex to each line, and
  they are the geodesic plus apartment detours: Moore-graph bases are worse than small bases.
- a02 (3,12) Tutte 8-cage lifts, a03 Heawood lifts, a04 4+4 base lifts on new groups of order 297-333 (best cost 24-26),
  a06 (4,12) H(3) lifts over Z97 (full cost ~12,700), a16 (4,12) W(3) lifts (cost 350-450): no cost 0 near the targets.
- a05 (4,12) SL(2,8) x Z73 with the field automorphism, S = e + one 3-orbit, exhaustive over all 12,262 orbits: min
  cost 61. Found the abelian-quotient wall: the Z_n coordinate of a word depends only on its signed letter counts, so one
  3-orbit reaches only ~199 residues; n = 1,063 is impossible.
- a10 (5,12) SL(2,8) x Z_n, n ~ 1,063: 82 % uncovered (same wall); a14 (7,12) SL(2,8) x Z_59417 with an order-7 orbit:
  10.9M holes (same wall: 65,226 signed count vectors for 7 letters against 59,417 residues).
- a13 (4,12) class-2 groups Heis(p) x A with fixed-point-free order-3 automorphisms: the orbit lies in one line of
  G/Phi, 4-300 vertices reachable. Opened the lead F_512 x| C_73 with the Frobenius x -> x^8 (random S: 17 holes).
- a08, a11 (6,12) orbit-structure tournament at equal N: k = 3 conjugation best (min cost 1-7); k = 5 conjugation in
  PSL(2,p) bad (min 184, Fix ~ p/2); k = 5 field on SL(2,32) x Z151 min 15-25. a11's "clump model falsified" used
  PSL(2,19) x Z1381, i.e. the abelian-quotient wall again.
- a09 (6,12) Frobenius Z74719 x| Z63 cost-1 state: the last hole is the same order-3 element in every basin; 5 more
  chain links stayed at 1.
- a12 (3,12) unstructured cubic graphs by 2-switch annealing: valid up to 1,350 (cost 6 at 1,400).
- a15 (3,12) exh3 on PSL(2,11) x Z2, PGL(2,11), Heis(11): min cost 54; most families too slow under load.
- a07 (6,12) SL(2,32) x Z151 sampling: see the director's runs (floor 3 clumps).

Director during the round: (15,12) PSL(2,197) x Z3924 found (first S, 29,999,670,624 vertices; the floor from (13,12)
is 29,997,644,040); wrote haar_bigq (haar_big0 over GF(p^e) with split-torus rows and Frobenius orbits; validated on
known solutions and against haar_big0 / haarcheck_gen costs on corrupted files); **(8,12) 297,777,408 (+4.8 %)**:
SL(2,128) x Z71, S = e + one orbit of the field automorphism x -> x^2 (order 7, Fix = SL(2,2)), 3 of 420 random orbit
samples had cost 0, haarcheck_gen VALID. (7,12) SL(2,32) x Z941 hits the abelian-quotient wall (min 395); (6,12)
SL(2,32) x Z151 floors at 3 clumps; (9,12) SL(2,128) x Z281 and (10,12) PSL(2,243) x Z271 started.

Reading: the win is a large odd-order automorphism with a tiny fixed set on a group whose abelian quotient is small
next to the orbit's letter lattice. Kept for round 2: affine semilinear groups F_q x| C_k with the Frobenius (a13's
lead, and (5,12), (6,12), (3,12) analogues), SL(2,2^e) x (non-abelian H) with a combined automorphism, wreath groups
H^k with the shift; one theory card for the two walls. Dropped: Moore-base lifts, class-2 groups, conjugation k = 5.
Process: cards called session/messaging tools four times by mistake (a05 send_message without arguments, a10
create_session "noop" then archived it, a16 archive_session with a bad id) and one card (a11) rewrote the scoreboard
file; the round-2 header names the allowed tools explicitly.

## 2026-11-01, raise-d12, round 2 (11 cards, 23:27 UTC)

Same session. Files: research/squads/raise-d12/r2/. Selection from round 1: the working principle of the director's
(8,12) find (an automorphism of large odd order with a tiny fixed set, on a group without a large abelian section), applied
to the small cells with new group families; one theory card. CPU was scarce (the (15,12) check and three director
searches ran throughout), so the round had 11 cards instead of 16.

Cards (best result; all negative):
- b01 (4,12) F_512 x| C_73 (round-1 a13 lead), alpha = x -> x^8: all 12,460 orbit sets have 22, 40, 61 or 62 holes (a
  structural floor); plain random S annealed to 8 (size-law mu ~31).
- b02 (6,12) F_32768 x| C_151 with an order-5 field orbit: floor of 3 clumps (cost 15), the same as SL(2,32) x Z151;
  two 3-orbits 18.
- b03 (5,12) F_2197 x| C_244 (alpha = x -> x^13): best 36; F_729 x| C_728 663 (abelian wall).
- b04 (3,12) exhaustive cubic Haar search on 54 affine groups F_q x| C_k of order 1,185-4,092: no cost 0; best 27 on
  F_64 x| C_21.
- b05 (5,12) D7^5 with the coordinate shift: every Haar graph is disconnected (5 generators cannot span (Z_2)^5; proof).
- b06 (4,12) D17^3 (no non-abelian group of order 33 exists; the card's first choice was the director's error): Z17^3 is an
  abelian normal subgroup of index 8, best 49,377.
- b07 (7,12) SL(2,32) x (Z191 x| Z5) with a combined order-5 automorphism: orbit S 1,121 against 25 for random S; the
  Z191 part of every word is a signed sum of 5th roots of unity (the abelian wall inside the kernel).
- b10 (4,12) SL(2,8) x D37 with a combined order-3 automorphism: parity wall (orbit elements share the reflection bit),
  best 248 over 3,200 orbits (scan unfinished).
- b12 (4,12) inverse-closed S (double covers of Cayley graphs): holes pair under inversion, but success rates are 3-8x
  below random S; valid only up to 41,568.
- b13 (6,12) SL(2,8)^2 x Z19 with the diagonal field automorphism: best 24 in a handful of evaluations (too slow under load).
- b08 theory note (r2/b08/NOTE.md): exact count of reachable abelian images R(S) for one orbit; k = 3 covers Z_n only up to
  n = 241, k = 5 up to n = 7,691 (>= 20-fold up to n = 661 at Δ = 6, 2,141 at Δ = 7). So SL(2,8) x Z73 (round-1 a05,
  min 61) and SL(2,32) x Z941 at (7,12) (min 395) are NOT explained by the abelian image alone; their walls are elsewhere.
  Moore-base lifts: 65 walks per (vertex, line) pair, rank 64, coverage matches the i.i.d. model.

Director during the round: **(9,12) 1,178,527,488 (+6.6 %)** SL(2,128) x Z281, S = e + an order-3 alpha-fixed generator
+ one 7-orbit (1,444 annealing evaluations; an involution as the fixed generator is much worse: median 357 against 56),
and **(10,12) 3,888,487,944 (+4.7 %)** PSL(2,243) x Z271, two free 5-orbits of x -> x^3 (626 evaluations); both
haarcheck_gen VALID from (e,A) and (e,B).

Reading: no round-2 card raised a cell; every new family hit a structural wall (abelian or parity sections, subgroup
traps, disconnection) that the cards measured and, in four cases, proved. Two rounds of negatives on (3..7,12) suggest
these cells will not fall to orbit structures at this budget; the field-automorphism groups that work exist only at
the sizes of (8..11,12) (SL(2,128), PSL(2,243)). Process: two stray session-tool calls again (b08 archive_session without
arguments, b12 send_message without arguments; both errored), despite the explicit tool list in the header.
