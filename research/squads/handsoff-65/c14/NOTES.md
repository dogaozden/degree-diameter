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
