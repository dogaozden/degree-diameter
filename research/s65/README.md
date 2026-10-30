# squad-6-5: bipartite (6,5) above 684 (Oct 29-30, 2026)

Goal: a bipartite graph of maximum degree 6 and diameter 5 on more than 684 vertices (table value 684, a Haar graph of
C6 x (C19:C3); Moore bound 1,562). Opus director + Haiku squad rounds (research/squads/s65r*/, log in
research/squads/LOG.md). Result so far: **no graph above 684**; the work below narrows where one can be.

## Tools (research/s65/tools/)

| tool | what it does | calibration |
|---|---|---|
| `score65` | scorer: unordered vertex pairs at distance > 5 | 684 record: bad 0 |
| `apsp` | all-pairs check (copy of research/lifts/coordinator_check/apsp.c) | |
| `haarex2` (+ `haarex2.g`) | exhaustive orderly Haar search H(G,S), \|S\| = 6 (job fresh-6-5) | |
| `mcos.c` | annealer for multi-orbit coset graphs: G acts on each colour class with orbits G/H_o, H_o cyclic; TYPE "1\|1" = Haar, "2\|2" = bi-coset, "1\|2,2" = G regular on side A and side B = G/K1 u G/K2, ... | "1\|1" re-finds the 684 graph in 47 s, the cost-2 wall of SmallGroup(351,5) in 20 s |
| `dcenum.c` | bi-coset graphs B(G;H,K): exhaustive unions of double cosets or annealing (fixed fast version from beyond-haar-d5b) | |
| `vl.c`, `kopt.c` | lift annealer; exact k-opt (all changes of K voltages) to cost 0 | |
| `kdesc.c` | exact steepest descent over all 1- and 2-voltage changes, branch and bound on the cost | |
| `../tabu/tabu.c` | tabu search over single-voltage changes (written by squad card s65r3-c6 from kdesc.c) | 672: 4 vs annealing 8; 704: 6 vs 12-14; finds the 684 Haar graph in 0.9 s |
| `vk.sh` | annealing + exact 2-opt pipeline | VALID lifts on 640 vertices (order 160) |
| `haar2lift.py`, `bicay2lift.py`, `normlift.py` | Haar / bi-Cayley graphs as 2+2 lifts by an index-2 subgroup; re-normalise tree voltages | same score65 as the originals |
| `sdhaar.c` (+ `.g`) | self-dual Haar graphs (phi(S) = S^-1) | fails the positive control (no side-A cover on the 684 group) |
| `bicay.c` | bi-Cayley graphs (2 orbits meeting both colours), from the previous session of this job | |

## Results

- **Haar graphs, orders 352-360** (704-720 vertices): exhaustive haarex2 over the low-involution groups (<= 3
  involutions), table in `haar/STATUS.md`; no Haar graph of diameter 5. Side-A covers (side B then 2+ short) only in
  SmallGroup(360,53), (360,55), (360,56). Annealing over the 260 groups with more involutions: best cost 4.
- **Non-Haar coset graphs**: |H| = 2 at 686-720 (non-Haar pairs only after round 1; a bi-coset graph B(G;H,H) with an
  index-2 normal subgroup N not containing H is a Haar graph of N), best 8 (SmallGroup(720,439)); |H| = 3 at 1035-1080,
  best 12 (3.A6, exhaustive optimum 12); |H| = 4: only Haar-type pairs at orders 4p.
- **2+2 lifts** (orders 160-180): exact 2-opt after annealing solves 640 vertices (calibration), not 672; tabu reaches
  lift cost 4-6 at 704-720; the Haar near misses of 360_53 and the best bi-Cayley near miss (704), written as lifts, have
  no cost-0 2-opt neighbour.
- Other families (all far): tri-Cayley (10 at 690), 3+3 lifts (28 at 696), alpha-invariant 2+2 lifts (38), multi-orbit
  "1|2,2" (27), vertex deletion + rewiring of near misses (1428 bad pairs at 686).
