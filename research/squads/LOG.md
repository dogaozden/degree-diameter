# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:05–19:45 UTC, cell-16-8 (Opus, cloud), goal: beat (16,8) = 36,201,060, round 1

Context: the table value is 45·|H(13)| = 9 × the (16,7) table graph (5·|H(13)|), i.e. DGQ's D = 8 family is
m = 5·(ceil(q/2)+2) copies of the generalized hexagon H(q) with 2 extra edges per vertex. The round tested which
structure of Z_m-lifts of H(q) + 2 matchings scales with q, at q = 3 and 5 (DGQ formula: m = 20 and 25), scorer
`research/d16D8/hexlift2 eval` (all sources). Folder `research/squads/d16D8-r1/`.

| card | idea | best VALID m at q=5 | at q=3 |
|---|---|---|---|
| c1 | Z_5 x Z_k skeleton (X(M) of the table), anneal the Z_k parts | – (k=5: cost ~200 on 100 sources) | 25 |
| c2 | incident jumps (two perfect matchings of H(q)) | – | 20 |
| c3 | jump distance 1 / 3 / 5 vs random bijections | – | – |
| c4 | flag shifts from a (q+1)-edge-colouring | 13 (unannealed random) | 24 |
| c5 | plain annealing push | 13 | 26 |
| c6 | flag shifts from line-local coordinates | – | 24 |
| c7 | group choice (Z_m vs products) | (pending) | |
| c8 | targeted repair moves | – | 28 |

Verdict: nothing reaches the DGQ formula at q = 5 (25); the best unstructured result falls from 28 (q = 3) to 13–16
(q = 5) while the formula rises. Incident jumps and algebraic flag shifts are worse than random. The squad confirmed
the lifts session's conclusion (DGQ's D = 8 graphs are ~2.5x better than random lifts of their family). Kept: nothing
from this family. Next: Opus switches to bipartite route-chart lifts at D = 8 (controller x F_q^7), see
research/squads/cells/d16D8.md.

## 2026-10-25 12:35–13:15 UTC, cell-16-8 resume (Opus, cloud, session_01CooNNbQpdKF6QpgaAQ3ukA), round 2

Goal: (16,8) = 36,201,060 = 45·|I(H(13))|. Round 1 tested lifts of H(q) at q = 3, 5, where DGQ's advantage has not
appeared yet, and H(13) checks are too slow for search. So round 2 used a TESTBED with the same degree q+3 and the same
walk-count scaling: Z_m-lifts of the incidence graph of the quadrangle W(q) + 2 matchings at diameter 6 = 4 + 2
(W(13) has 4,760 vertices; a full check takes 1-3 s). DGQ-analog targets 5·⌊(q+5)/2⌋: 30 (q=7), 40 (q=11), 45 (q=13).
Scorer `research/d16D8/baselift eval FILE 6` (all sources). Folder `research/squads/d16D8-r2/`.

| card | idea | VALID m at q=13 | q=7 | q=11 |
|---|---|---|---|---|
| c1 | plain annealing frontier (warm starts, bad-source repair) | 14 | 16 | 12 |
| c2 | Z_5 x Z_k level skeleton (D=5 cover with k sheets) | 5 (k=1 only) | 10 | 5 |
| c3 | algebraic flag voltages (PG(1,q) parameter, Singer index, dlog) | 14 (random flags) | 16 | 12 |
| c4 | designs invariant under a semiregular C ≤ PSp(4,q), order (q²+1)/2 | **28** | 20 | 24 |
| c5 | other level skeletons (L, t1, t2) x k sheets | k = 1 only | | |
| c6 | rainbow colouring (q+3 = 2(k-1)) with Z_5 skeleton | 0 (refuted) | 18 (injective, no levels) | |
| c7 | targeted repair: change one edge on a walk to fix an uncovered triple | **23** | 18 | |
| c8 | voltages on flags only (matchings 0) | 14 | 16 | 12 |

Opus checked c4 (m=28) and c7 (m=23) at q=13: baselift VALID(all sources), and research/d16D8/checkgq.py confirms
W(13) flags + exactly two point->line perfect matchings. Kept: symmetry (c4) and targeted repair (c7), the only ideas
above random (random designs: VALID to m = 12-14). Refuted: every level skeleton with more than one sheet (worse than
unstructured lifts), algebraic flag voltages (they act like potentials), the rainbow hypothesis. Opus side results:
typed levels (H and its dual, identity on friendly transitions) anneal worse than untyped (1026 vs 118 uncovered at
q=3, m=25); a local "full-coverage" design search (research/d16D8/localdes.c) reaches only m = 12 (q=7) and 16 (q=13);
Z_k-covers whose geodesics between every opposite pair hit all k sheets do not appear to exist even for k = (q+1)/2
(research/d16D8/geocov.c plateaus at 14% of pairs missing a sheet, q=5, k=3). Next: symmetric + repair on the hexagon
itself (H(5) with C_31, H(7) with C_19; research/d16D8/hexsym.py, symbase.py, symrepair.c).
