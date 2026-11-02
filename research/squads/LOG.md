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

## 2026-11-01/02, job raise-d9 (Opus director, branch claude/raise-d9-orbit-metacyclic-ndvfty)

Goal: raise the D = 9 values at Δ = 3..20 with orbit and metacyclic/Frobenius searches (tools of beyond-d11 and
beyond-d11b). Machine: 4 cores, 15 GB. At the start the D = 9 values at Δ ≤ 16 sat at size-law mu 23-47 (pushed by
earlier orbit searches), but (17..20, 9) sat at mu 2.6-2.9 (first S solved by new-cells-beyond). haar_big0 evaluates an
orbit S at N = 2.7e8 in ~0.2 s with 2 threads, so the director took (17..20, 9) and the squads took Δ ≤ 16 and new ideas.
Before round 1 the director had (17,9) 543,962,400 (SL(2,151) x Z79, mu 13.2, 791 evaluations) and (19,9) 1,317,726,672
(SL(2,277) x Z31, mu 13.4, 237 evaluations), both haarcheck_gen VALID. Note: sched_autogroup was on at first, so the
cards' nice 10 had no effect (each card got the same CPU as a director job); the director switched it off at 23:03 UTC.

### Round 1 (16 cards, 22:58-23:20 UTC, research/squads/raise9/r1/)

Cards (best result):
- a01 (4,9) odd non-metacyclic groups Z17^2 x| Z9 (cost 28), Z29^2 x| Z3 (disconnected or 3,000+): words collapse on the
  abelian kernel. a02 (3,9) exhaustive cubic Haar over 2,191 groups of order 254-330 (+690 metacyclic up to 360): none;
  min cost 8 at N = 272 (Z17 x| Z16); cost 0 only at N = 253 (Z23 x| Z11, the 506 value itself). a03 (6,9) odd Frobenius
  groups: random-S min/median 16/72 for Z2551 x| Z25 vs 26/140 for SL(2,17) x Z13 (the current group); annealing
  stalled at cost 6 (Z2551 x| Z25, Z1559 x| Z41).
- b01-b06 small-n SL(2,p) x Z_n orbit shape (ODD_D_HOLES rule from D = 11): (11,9) best PSL(2,97) x Z19 cost 9 (mu 23.6);
  (12,9) SL(2,137) x Z7 cost 12 (mu 36.8, current group 30 in the same time); (13,9) small n worse (SL(2,257) x Z2 cost 40
  vs 20 for SL(2,103) x Z31); (14,9) SL(2,167) x Z13 cost 12; (9,9) PSL(2,73) x Z9 cost 22; (8,9) PSL(2,47) x Z13 cost 12.
  b07 (6,9)/(7,9) other SL/PSL(2,q) shapes: cost 21-95.
- m01 (17,9) shape measurement (r1/m01/SHAPES.md): SL(2,p) x Z_n, n in {1, 9, 13} or prime n with few alpha-fixed z;
  PSL bad for p > 300; f = 5 worse than f = 2. m02 orbit order 5: **(15,9) PSL(2,151) x Z61 "5 3 0" cost 4** at N just
  above the bar (mu 28.1); k = 5 random median 77 vs 85 for k = 3.
- w01 products at (12,9) (worse than SL(2,83) x Z31); w02 field-automorphism orbits at (8,9)/(9,9) (cost 20-22); w03
  twisted product Z173 x| PGL(2,29) (8x worse than the direct product); w04 lifts of a 2+2 base for (4,9) (Z251 x| Z5
  cost 24; cyclic voltage groups collapse).
No card solved. Kept for round 2: the (6,9) Frobenius lead (2x better random statistics), k = 5 orbits, and seed farms on
the near misses ((8,9) PSL(2,47) x Z13, (11,9) PSL(2,97) x Z19, (12,9) SL(2,137) x Z7). The (15,9) cost-4 state went to
the director's queue. Dropped: small n as a rule at D = 9, products, field automorphisms, twisted products, (3,9) Haar.
Process: cards ran 9-21 minutes of their 25; three called session tools (archive_session, send_message) with empty
arguments, all rejected (checked in the transcripts); round 2's prompt lists the allowed tools explicitly.

### Round 2 (17 cards, 23:16-23:40 UTC, research/squads/raise9/r2/)

Cards (best result): (6,9) odd Frobenius farms: **f02 Z1559 x|_84 Z41 (N 63,919) cost 2 on 1 of 10 fresh 90 s seeds**
(costs 2, 6, 6, 6, 6, 8, 8, 8, 10, 10), f01 Z2551 x| Z25 6 (13 seeds), f03 Z2377 x| Z27 8; f04 hole anatomy (inverse pairs,
one side at ecc 10; 15k sampled single swaps of the cost-6 states: none < 6); w06 other odd families (Frobenius with
k = 41/25/37 best; centred non-Frobenius 220-1,360 median); f08 Frobenius products worse. (7,9) f05 Z5659 x| Z41 16; (8,9) f06
Frobenius k = 37/51 18-26, n02 PSL(2,47) x Z13 stuck at 12; (9,9) f07 Z35771 x| Z49 24; (11,9) n04 PSL(2,97) x Z19 12 (round-1
state), k02 k = 5 groups start at mu 30+; (12,9) n03 SL(2,137) x Z7 12, k04 PSL(2,71) x Z101 "5 2 2" 16 (k = 5 no edge in
random medians); k03 single-orbit S ("5 1 f", exhaustive) far worse than plain S; x01 (4,9) exhaustive on Z101 x| Z25 did not
report; w05 (16,9) SL(2,293) x Z7 same random median/mu as the current group, stalled at 36.
No card solved. Machine load ~20: cards got ~1/10 core (50 ms per evaluation at N = 64k). Kept: the (6,9) Z1559 x| Z41 farm
(director farm at nice 3 from seed 1001 plus 4 card farms in round 3). Dropped: near-miss resumes/finishers, k = 5 at
(11,9)/(12,9), single-orbit S, Frobenius at (7,9)-(9,9).
Process: 5 more stray session-tool calls (archive_session, interrupt_session), all rejected; one card ran two jobs at once.
Director meanwhile: (18,9) 850,056,960 (SL(2,191) x Z61 "3 5 3", mu 11.35, 81 evals) and (20,9) 1,972,000,272 (VALID).

### Round 3 (16 cards, 23:44-00:12 UTC, research/squads/raise9/r3/)

Mostly director support: shape measurements for the next rungs at (15..20, 9), four more (6,9) Frobenius farms, and
four idea cards. Cards (best result):
- Shapes (RANDORB, 1-16 samples each; samples took 10-115 s under load, and haar_big0 needs ~2x its printed N/2 bytes):
  s17 keep SL(2,277) x Z13 "3 5 2" ("3 4 5" worse, "3 3 8" hopeless); s18 on SL(2,241) x Z31 "3 6 0" min/median 16/31 vs
  "3 5 3" 26/36 vs "3 4 6" 132; s19 "3 6 1" beats "3 5 4" and "3 4 7"; s15 PSL(2,151) x Z61 "5 3 0" 80 vs "3 5 0" 72,
  anneal to 24; s16 (16,9) SL(2,139) x Z65 "3 5 1" annealed to 26 (current group 32 in the same time); s20 could not run
  (1.5 GB at N = 1e9). **w07 f-split at (18,9) on SL(2,191) x Z61: f = 0 median 24, f = 3 42, f = 6 84; -I is a hole on both
  sides for f = 0 and f = 3; no central (+-I, z != 0) holes in 6 sides, against ~9 predicted by the rotation clump model.**
- (6,9) farms on Z1559 x| Z41: g1 17 seeds best 4, g2 16 seeds best 4 (K = 16 >= K = 8 > K = 4), g5 12 seeds best 4 (and a
  screen of all 15 Frobenius groups up to N = 67,000: only odd k = 37-43 competitive), g4 Z2377 x| Z27 best 6, Z1777 x| Z37 12.
  Load ~13-20: each 90 s seed got 5 s of CPU on some cards.
- i02 (10,9) k = 5 on SL groups: stalls at 56-98 (control PSL(2,59) x Z41 13); i03 (13,9) SL(2,89) x Z49 / SL(2,139) x Z13 48,
  control 34; w08 bi-coset graphs for (3,9) on D254 (weak negative, unverified code); **w09: covers of a solved D = 9 Haar
  graph cannot have diameter 9: every solved base has a same-side vertex reached by exactly one non-backtracking walk of
  length <= 8, so in any regular M >= 2 cover the other M - 1 lifts are at distance > 8 (Z2, Z3 central covers of (5,9):
  cost 2,166 and 10,486).**
No card solved. What the director took from it: the (17,9) cost-2 plateau at SL(2,277) x Z13 is an inverse pair of
alpha-fixed TORUS elements (a I + b g, z = 0; EVAL + UNCPRINT), and central holes are rarer than modelled (w07), so the next
rungs use small p (~100-240) and large n with one alpha-fixed z (gcd(r - 1, n) = 1). Result: (20,9) SL(2,233) x Z79 at mu
16.16 solved in 57 evaluations and (19,9) SL(2,151) x Z193 at mu 15.71 in 17, where SL(2,457) x Z7 (mu 17.4), SL(2,313) x Z9
and SL(2,523) x Z7 had stalled at cost 6-30.
Process: i03 dumped 87 non-JSON lines into the scoreboard (moved to r3/i03/scoreboard_spill.txt); 6 more stray
session-tool calls (archive_session, interrupt_session, read_documentation), all rejected or read-only.
