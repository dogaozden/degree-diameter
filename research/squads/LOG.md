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
