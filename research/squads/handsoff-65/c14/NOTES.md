# c14 notes (re-coordinatise near misses as lifts with bigger bases)

Start 17:46 UTC. Deadline 19:45 UTC.

## Setup
- G176.txt = SmallGroup(176,17) = C11:Q16 table (copied from c1/tabs/sg_176_17.txt).
- base704.sol = c1's 2+2 base [[2,4],[4,2]] with the cost-4 voltages (c1/sols/s176_17_a2_13.sol).
  `vl base704.sol G176.txt` EVAL: cost 4; export gives the 704 graph with bad=352.
- subgroups.py GROUP: conjugacy classes of subgroups (subs176.txt: order, #gens, elements).
  Classes of G176: order 88 x3, order 44 x3, order 22 x1, order 16 x1, order 11 x1, order 8 x3, 4 x3, 2 x1, 1.
- subquot.py SOL GROUP NELEMS OUTBASE OUTGROUP: the N-lift re-coordinatisation (vertices (a,i) <-> (a, n t_i),
  edge (a,i)-(b,j) voltage nu where t_i*al = nu*t_j). Then normlift.py normalises the spanning tree.
- Check: for each order-88 class, the 8+8 base (24 edges) lifted by N gives the same 704 graph (export_lift +
  score65: bad=352 for all three classes). vl cost of the N-lift = 8 = k * 4 (sources are counted per fibre
  copy), so cost 0 still means diameter <= 5.

## Runs
- tabu INIT=sol 60 s on the three 8+8 N-lifts (group order 88): best stays 8 (= start) for sub 1 and sub 2
  (606 and 659 steps). No descent at all from the start point.

## Results so far (17:46-18:11)
All re-coordinatisations are verified: export_lift + score65 gives bad=352 (704 graph) or bad=360 (720 Haar) for every
N-lift, so the graph is the same and only the move set changes.

| start graph | base (total vertices x group) | start cost | runs | best |
|---|---|---|---|---|
| 704 C11:Q16 (c1 cost-4) | 4 x 176 (2+2) | 4 | tabu 3 s (earlier c1 runs: 4) | 4 |
| same | 8 x 88 (4+4, 3 subgroup classes) | 8 | tabu 60 s x3 (606/659/506 steps); SA SWAP=0.3 60 s; kdesc 1-/2-change exact (1.0M candidates) | 8 |
| same | 16 x 44 (8+8, 3 classes) | 16 | tabu 45 s x3 | 16 |
| same | 44 x 16 (22+22, 1 class) | 44 | tabu 60 s; exact 2-change kdesc (878k candidates, 179 s) | 44 |
| same | 8 x 88 ILS (STALL 150 KICK 4, 240 s, 1607 steps, 10 restarts) | 8 | | 8 |
| 704 graph #2: SmallGroup(176,40) cost-4 (c1 s176_40_a1_82) | 8 x 88 (7 classes) | 8 | tabu 40 s x2 | 8 |
| 704 random start in 4+4/88 base (tabu INIT=random) | 8 x 88 | - | 50 s x2 | 44, 46 |
| 720 Haar 360_53 (vl base 1+1, S recovered: A_x ~ B_{x s}, S = 30,54,103,122,195,211 in gap_tables indexing) | 4 x 180 (2+2) | 4 | tabu 40 s | 4 |
| same | 6 x 120 (3+3, 2 classes) | 6 | tabu 40 s x2 | 6 |

Random-start 4+4/88 lifts reach 44 (c2 reports 35 for p=4 N=704 sg_88_1 after 9 min), so the cost-4/8 start is an
exceptional point, but every move set I tried leaves it as a strict local minimum (exact 2-opt at the 4+4 and 22+22
levels, tabu/ILS/SA with base 2-switches).

## Results (18:00-18:36)
More N-lift starts, all verified (bad count of the N-lift graph equals the original):
- 720 Haar, index 3 (3+3, group 120, 2 classes), index 4 (4+4, group 90), index 5 (5+5, group 72), index 6 (6+6, group 60):
  start costs 6, 8, 10, 12. tabu 40 s each: no descent (best = start).
- 720 Haar, 2+2 by 180: ILS (tabu with STALL 200 KICK 4, 240 s, 2732 steps, 13 restarts): best 4.
  Exact 2-change descent (kdesc, 1.12M candidates): no improvement. Random-start tabu 60 s: best 16.
- 704 (2+2 by 176, the cost-4 start): ILS (STALL 300 KICK 4, 240 s, 2990 steps, 9 restarts): best 4.
- 704 cost-4 solutions s176_17_a2_14 and r_s176_17_a2_13_51 (order-88 N-lifts): tabu 40 s each: best 8 (start).
- 704 cost-4 from order-176 group #40 (c1 s176_40_a1_82): all 7 order-88 classes give cost 8; tabu 40 s x2: 8.
- 704 2+2 kopt K=2 (exact, cost-0 search, 1.07M candidates): none.
- 704 4+4/88 exact 2-change descent: none. 8+8/44 exact 2-change descent: none (67 s). 22+22/16 exact 2-change: none (878k).

## c5's 732 mcos near miss (bad 915), now as an N-lift
- c5/deep/1_3-3-3.sg_366_2.best.edges is G-invariant under left multiplication when B orbit j is labelled by the mcos
  coset convention (right cosets g<2>, index = rank of the minimal element), so the labelling is recovered (c14/c5check.py).
- c14/c5quot.py ORDER: quotient by the unique subgroup N of that order (coprime to 3 so N acts freely on all 732
  vertices). N = C61: base 6+6 (36 edges), vl cost 30, tabu 60 s: 30 (no descent). N = C122: base 3+3 (18 edges),
  vl cost 15, tabu 60 s: 15 (no descent); random-start tabu on the same base: 40. kopt K=2 on both: no cost-0 neighbour
  (1.1M candidates each). The bad count of each quotient-lift is still 915.

## Status at 18:36
Every move set I tried (1-change, 2-change exact, tabu, ILS with kicks, SA with base 2-switches) leaves each of the
near misses (704 cost 4, 720 cost 2-4, 732) as a strict local minimum. Random starts in the same families reach only
cost 16-44 in a minute, so the good starts are rare structured points and the search cannot move between them.
Tools for the coordinator: c14/subquot.py (any voltage lift -> N-lift), c14/subgroups.py (conjugacy classes of subgroups),
c14/c5quot.py (quotient of a coset graph by a semiregular subgroup), c14/test_haar360.py (recovering a Haar set S).
