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
| `haarex3.c` | haarex2 with the sixth element solved exactly (linear forms, square roots, conjugators) | same side-A covers and VALID sets as haarex2 on SmallGroup(342,12) and (360,53); 4x faster |
| `sdhaar.c` (+ `.g`) | self-dual Haar graphs (phi(S) = S^-1) | fails the positive control (no side-A cover on the 684 group) |
| `bicay.c` | bi-Cayley graphs (2 orbits meeting both colours), from the previous session of this job | |

## Results

- **No Haar graph on 686-720 vertices.** Every one of the 353 non-abelian groups of order 352-360 was searched
  exhaustively for a 6-element S with H(G,S) of diameter 5 (haarex2 for the 93 groups with <= 3 involutions, 24 of
  them in job fresh-6-5, and 5 more; haarex3 for the other 255, round s65r7): none exists. Abelian groups give at
  most 542 vertices (fresh-6-5's counting bound), and fresh-6-5 closed orders 343-351 the same way. Side-A covers (side
  B then 2 or more short) occur only in SmallGroup(360,53), (360,55), (360,56), (360,125), (360,126), (360,136), (360,138). Check script and
  lists: `haar/all_352_360.txt`, `haar/STATUS.md`; logs in research/squads/s65r2-s65r7/c*/h*.log.
- **No Haar graph on 722-760 vertices either**: all 151 non-abelian groups of order 361-380 closed (40 in round s65r4,
  111 in round s65r8; side-A covers only in 372_1 = C31:C12). So the 684 record is the largest Haar graph of degree 6
  and diameter 5 below 762 vertices. `python3 research/s65/haar/check_closure.py` re-derives `haar/STATUS.md` from the logs.
- **Non-Haar coset graphs**: a bi-coset graph B(G;H,H) with an index-|H| normal subgroup N meeting H trivially is a Haar
  graph of N, so sweeps keep only the other H (`SKIPHAAR`). |H| = 2: orders 686-720 and 704 (all groups), best 8
  (SmallGroup(720,439)); |H| = 3: only orders 1050/1053 have non-Haar pairs (best 150); 1080: best 12 (3.A6, exhaustive
  optimum 12); |H| = 4: only Haar-type pairs at orders 4p.
- **C3 x P256 (768 vertices)**, the analogue of the vertex-transitive (5,5) record (C3 x SmallGroup(128,139), |H| = 2;
  calibration: the same pipeline re-finds it, and it is the only cost-0 pair among the 231 non-Haar pairs of C3 x P128):
  about 1,500 pairs over the 4,284 groups P with <= 11 involutions and 400 with 15, median ~100 of 768; best 14 for
  C3 x SmallGroup(256,357), H = K (three 120 s anneals stay at 14; neighbours 256_362, 256_413: 22), a cluster of
  2-generator class-5 groups like the record's P128; semidirect C3 : P256 best 62.
- **2+2 lifts** (orders 160-192): annealing + exact 2-opt solves 640 vertices (calibration), not 672; tabu reaches lift
  cost 4-6 at 704-720, 22-36 at 768. The Haar near misses of 360_53 (bad 360, the closest graphs above 684 found here)
  written as 2+2, 3+3, 4+4 and 8+8 lifts have no cost-0 2-opt neighbour, and tabu does not move them below cost 4.
- Other families (all far): tri-Cayley (10 at 690), 3+3 lifts (14 at 696 with tabu), alpha-invariant 2+2 lifts (38),
  bi-Cayley (4 at 704 with annealing), multi-orbit "1|2,2" (27), self-dual Haar (no side-A cover even on the 684 group),
  vertex deletion + rewiring of near misses (1428 bad pairs at 686).
