# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26 06:20 UTC: job new-3-7, goal beat (3,7) = 168, round 1

Session: claude/bipartite-d3-d7-search-9kfg4g (Opus). Brief and cards: `d3D7-r1/BRIEF.md`, `d3D7-r1/CARDS.md`.
Before the round, Opus ran exhaustive all-groups lift searches (Haar 85–127, 2+2 43–63, 3+3 29–42: none) and scanned
the vertex-transitive census (none). Ten Haiku cards, ~20 min each, on a machine at load 10–14:

| card | idea | best (n: cost) |
|---|---|---|
| c1 | salift over every group of order 11–16 (p = 6–8) | 180 (C15, p = 6): 12; 176 (C11): 20; 182 (C13): 26 |
| c2 | parallel tempering lift annealer | calibration (C7, p = 12, n = 168): 14, same as salift |
| c3 | +2 gadget in the 168 graph + sa3 repair | 170: 92 ordered pairs, never below the start |
| c4 | quotient of the 168 by C2, gadget in the base, re-lift | 172: 80 |
| c5 | lifts with a fixed-point-free order-3 symmetry | calibration Z14 p = 6 in 781 iterations (salift ~15 M); 180 (C10, p = 9): 18 |
| c6 | coset graphs, stabilisers of order 2, all 199 groups of order 170–200 except 192 (36 M graphs) | diameter 8 at best (180: 720) |
| c7 | Moore-tree completion | 170: 502 (worse than plain sa3) |
| c8 | polynomial graphs over GF(3), Z_m | diameter 8 at best |
| c9 | memetic GA over lifts | calibration C14 p = 6 in 13 s (salift ~45 s); 180 (D10, p = 9): 37 |
| c10 | SAT (python-sat, CaDiCaL) | times out on the calibration |

Kept: c5's symmetry speed-up and c9's GA. Opus's reading: c5's symmetric lifts with a free symmetry are lifts over a
semidirect product with a smaller base, so at covered orders they repeat the exhaustive searches (c5's 18 at C10 p = 9 is
exactly the exhaustive C30 3+3 optimum 6, times 3). Round 2 therefore goes to symmetries with fixed points, multi-orbit
coset graphs, permutation-voltage (non-regular) covers, and the GA on medium groups.
