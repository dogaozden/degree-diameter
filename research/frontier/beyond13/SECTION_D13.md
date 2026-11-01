### D = 13 at Δ = 3..10 and D = 14 at Δ = 3..8 (job beyond-d13, 2026-11-01)

Job beyond-d13 (Opus director + seven Haiku squad rounds of 15-16 cards, cloud session, branch
claude/beyond-d13-search-z35z61). Fourteen new cells (nothing was recorded at D = 13, 14 before), five of the lab's
D = 11, 12 values raised ((4,11), (5,11), (6,11), (4,12), (5,12)), and one 2013-table value beaten ((5,10), below). Size limit: at most about 20 billion vertices. Files:
research/frontier/beyond13/ (cells.txt and cells_other.txt list every value with its check; rows13.py makes the rows,
splice13.py puts them here; sols/, runs/ (haarcheck_gen logs), checks/ (apsp, metacheck), graphs/ (edge lists),
THEORY.md); squad cards and scoreboards research/squads/beyond13/r1..r7; log research/squads/LOG.md.

**What won where.**
- Δ = 3 (both D): cyclic voltage lifts of small cubic graphs, annealed voltages (squad r2/e16's lift.c), closed by an
  exhaustive 1-opt voltage scan with a tabu walk (r5/h02's scan.c): GP(10,3) x Z170 at D = 13 (3,400), Pappus x Z317 at
  D = 14 (5,706). Better than every Haar graph tried (A6 x Z4, 2,880, exhaustive pairs at D = 13; PSL(2,7) x Z15, 5,040 at
  D = 14), but not at D = 11, 12, where the lab's metacyclic Haar values stay ahead (r5/h10). Why lifts work
  (r3/f03 LIFTS.md, r4/g11 LIFT_BOUND.md, THEORY.md section 2): a Z_n lift's walk ends where its net traversal vector says;
  GP(10,3) keeps 82 % of its 24,574 nonbacktracking walks of length <= 13 distinct. Upper bound for Z_n lifts of a base:
  n <= min over pairs of the number of distinct net traversal vectors (GP(10,3): 647 at D = 13, 1,197 at D = 14).
  Practical note: lift.c cools over L evaluations (default 20,000), so short runs need L ~ 1,000 (r4/g01).
- Δ = 4, 5 (both D): Haar graphs of metacyclic groups Z_m x|_r Z_k of odd order (Frobenius groups when m is prime)
  and products of two, with random S (haar_gen3, or the director's bit-parallel hmeta). Two reasons, both measured: at odd D an odd-order group has no involutions and a Frobenius group has trivial
  centre, so the special holes of ODD_D_HOLES.md do not exist (THEORY.md section 1; r1/c14 measured -I missed by
  20-46 % of random S in SL); and at Δ = 4, 5 the alpha-orbit form is too rigid (one free element at Δ = 4, one random
  fixed generator plus one orbit at Δ = 5), so random S wins at even D too ((4,12), (4,14), (5,12), (5,14)). Small k
  fails: the group is nearly abelian (random-S word cover 1 % for k = 1, 6 % for k = 3, 97-99 % for k >= 11; r2/e11).
- Δ = 6..10: SL/PSL(2,p) x Z_n with alpha-orbit S (haar_big0). At D = 13, SL with small n (as at D = 11) and also
  PSL with moderate n (40-75) solved. A RANDORB screen of start costs before annealing (r4/g07) helped at (6,14). The
  metacyclic rule reached Δ = 6 only at D = 11 ((6,11) Z17203 x|_9845 Z61); at (6,13), (6,12), (6,9) it stopped at
  cost 2-6, and at Δ = 7 at cost 4-14 (r7/j14 RULE.md).
- (10,13) is at the 20-billion cap (PSL(2,503) x Z157, first S solved, λ = W/N = 31.8). (9,13) solved at mu 3.1, 5.1 and
  9.8 in 5-17 evaluations; (8,14) at mu 7.1 in 21 and at mu 12.1 in 146 evaluations; odd D needed chained links at mu 7-9 for Δ = 6, 7.

**Squad (111 Haiku cards in 7 rounds; LOG.md).** The ideas that moved the small cells came from cards: odd-order
groups (r1/c15), voltage lifts (r2/e16), products of Frobenius groups (r2/e12), the lift cooling fix (r4/g01), the 1-opt
lift finisher (r5/h02), metacyclic groups at even D (r4/g13, r5/h08), RANDORB screening (r4/g07), the test against the 2013
table (r6/i10, r7/j01). The mid cells (Δ = 6, 7) were raised 1-5 % by cards. The director: the plan and the selection between rounds, the (8,13), (8,14), (9,13),
(10,13) values and the (3,13) Z166/Z170 and (3,14) Z280 lifts, the checkers for graphs outside haarcheck_gen's families
(metacheck.py, metacheck2.py, tab2edges.py, meta2edges.py; all-pairs apsp on every graph below 5e5 vertices), hmeta and
liftd, THEORY.md.

**What failed or was not tried.**
- Orbit S inside metacyclic groups (alpha = scaling): costs saturate (r2/e03, e14, director). Lifts at Δ = 4, 5 (K4,4,
  PG(2,3), GQ(3,3), the biplane, random bases) stayed below the Haar values; K4,4 lifts are capped by the lift bound.
  Non-abelian voltage groups on GP(10,3): cost 2 at 3,300. Meta at Δ = 6 ((6,11), (6,13)): cost 2 at best.
- Near misses at cost 1-3 that did not close: (6,13) SL(2,59) x Z103 (the two holes are a transpose pair), (6,14)
  PSL(2,83) x Z331, (7,13) PSL(2,131) x Z139, (8,14) PSL(2,397) x Z181 (mu 12), (9,13) SL(2,677) x Z13 (mu 14, cost 12).
- The machine (4 cores, 15 GB) was the limit: the director's checks held 3-5 threads, so cards often ran at 5-10 % of a
  core. The (10,13) check was OOM-killed once after 58 min (a card's numpy checker plus a director search pushed the box
  over 15 GB) and was rerun; cards were then capped at 0.5 GB, which also capped what they could search at (7,14), (8,13).

**Side result inside the 2013 table: (5,10) >= 92,318.** Squad card r6/i10 tested the metacyclic idea on the old table:
the Haar graph of Z1567 x|_871 Z29 (order 45,443, random S, hmeta, 11 s) has 90,886 vertices, maximum degree 5 and
diameter 10 (apsp: checks/d5D10_n90886_meta1567_29.apsp.txt; metacheck: checks/d5D10_meta_1567_29_i10.metacheck.txt;
solution sols/d5D10_meta_1567_29_i10.txt), and the director closed i10's cost-1 near miss Z2687 x|_2416 Z17 (order 45,679) with hmeta chains (T0 = 8, REHEAT = 400): 91,358 vertices, apsp and metacheck VALID
(checks/d5D10_n91358_meta2687_17_2416.apsp.txt, sols/d5D10_meta_2687_17_2416_dir.txt).
Round-7 card r7/j01 then found Z1489 x|_61 Z31 (order 46,159): 92,318 vertices, apsp and metacheck VALID
(checks/d5D10_n92318_meta1489_31_61.apsp.txt, sols/d5D10_meta_1489_31_61_j01.txt), 2.5 % above 90,068.
The 2013 table (DS14v2, as copied in research/frontier/TABLE.md) has 90,068 for
(5,10), and the lab's harvest history has no (5,10) entry; literature after 2013 was not checked (TABLE.md says the same
for every D >= 7 cell), so these are candidates for the coordinator, not claimed records. The same card's (5,9) graph
(28,418, Z1093 x|_901 Z13) beats the 2013 value 27,936 but not the lab's 29,756 (harvested earlier, also metacyclic).
(4,9) and (4,10) near misses: Z101 x|_5 Z25 (5,050 vertices, cost 2) and Z109 x|_12 Z54 (11,772, cost 2) against 4,970
and 11,748 (r6/i09 and director chains).
