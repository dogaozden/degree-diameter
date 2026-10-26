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

## 2026-10-26 07:00 UTC: job new-3-7, goal beat (3,7) = 168, round 2

Session: claude/bipartite-d3-d7-search-9kfg4g (Opus). Brief: `d3D7-r2/BRIEF.md` (round 1 table and the
semidirect-product reduction added). Eight Haiku cards, ~25 min each:

| card | idea | best (n: cost) |
|---|---|---|
| r2c1 | memetic GA (r1-c9) on medium groups | 180 (C10, 9+9): 8 and (C3 × C3, 10+10): 8; (C15, 6+6): 12; 176 (C11): 20; 182 (C13): 26: the salift floors again |
| r2c2 | memetic GA, all groups of order 16 (p = 6), 12 (p = 8), 14 (p = 7) | 192: 32; 196: 42 |
| r2c3 | lifts with an order-3 symmetry with fixed points | calibrations fail; 182 (C13): 38 |
| r2c4 | lifts with an involution with fixed points | calibration at D = 5 works; 180 (C15): 960 vs 12 without fixed points |
| r2c5 | coset graphs, two orbits per side, stabilisers 1 and 2 | degree equations force |D_ij| = 2; 174 (|G| = 58, exhaustive): diameter 10 |
| r2c6 | permutation-voltage dipoles over AGL(1,q) (exhaustive, q = 89–127) and PGL(2,q) | 178: 3526 ordered pairs (random graph: 3576); 180 (PGL(2,89)): 2180 |
| r2c7 | permutation-voltage lifts of the 2+2 base over AGL(1,q) (exhaustive) and PSL/PGL(2,43) | 172: 1032; 176: 2006 |
| r2c8 | GH(2) + hub gadgets | 170: 398 |

Opus in parallel: the exhaustive 4+4 sweep (all groups of order 22–31) ended negative; 5+5 (17–21) found the best near
miss of the job, C3 × S3 at n = 180 (cost 4 = 36 bad pairs), which no annealer or tabu search could move in any
symmetry-broken frame. Spin-off: no 2+2 lift over any group of order 73–87 beats the (3,8) record 288.

Verdict: two rounds in a row added nothing; the symmetric families are exhausted and the low-symmetry regime is out of
reach of every search tried (none rebuilds 168 with C7 on a 12+12 base). Stopped. Notes: `cells/d3D7.md`.
Comparison note for the coordinator: the squads' main value here was breadth of negatives (seven new families tested in
~45 minutes of wall-clock), plus the GA speed-up and the fixed-point-symmetry calibrations; no card came closer than the
Opus exhaustive near misses.
