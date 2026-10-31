# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## Round sd6-r1 (Oct 31 2026, 08:40-08:55 UTC, job selfdual-d6, session claude/selfdual-haar-d6-drd2bl)

Goal: a (7,6) Haar graph on more than 9,592 vertices (|G| >= 4,797), self-dual or otherwise. Cards in
`sd6-r1/cards.md`, scorers `research/selfdual-d6/src/sdhi` and `haar_sd` (full check before any SOL), build_sdhi.py /
build_haar2.py + apsp for claimed graphs, scoreboard `sd6-r1/scoreboard.jsonl`. Before the round I had calibrated
(sdhi tabu): valid self-dual graphs up to N = 2,352 (SL(2,7) x Z7) and the counting model says a random-like S misses
about 686 elements at N = 4,797 (first-moment ceiling N ~ 2,450).

| card | direction | largest N solved (checked) | best uncovered at N >= 4,797 |
|---|---|---|---|
| c1 | self-dual sdhi, metacyclic C_m:C_k, N 2,105-2,325 | 2,107 (C43:C49, C301:C7; apsp VALID) | not run (2 at 2,325) |
| c2 | haar_sd plain vs self-dual, PSL/PGL(2,q) x Z_n | 2,184 (PSL(2,7) x Z13, both families) | not run |
| c3 | orbit-symmetric S, k = 3 (haar_sd ORBIT 3 2 1) | 2,352 (PSL(2,7) x Z14; I re-ran build_haar2 + apsp: VALID) | 505 (PSL(2,7) x Z31, 5,208) |
| c4 | psi of order 6 (sdhi ORDS=2,6) | none (best 25 at 2,184) | not run |
| c5 | Heisenberg groups (haar_sd heis q) | 2,197 (Heis(13), apsp VALID) | 481 (Heis(17), 4,913) |
| c6 | target-order measurement, 6 groups | - | 448 (SL(2,17), 4,896; model mu 728) |
| c7 | wildcard: AGL(1,q), polynomial S | 1,640 (AGL(1,41)) | 485 (AGL(1,71), 4,970); quadratic S worse (737) |
| c8 | wildcard: maximize distinct words | - | 437 (SL(2,17), 91.1 % covered; random S 82.8 %) |

No card came near the target: at N ~ 4,900-5,200 every method stops at 437-505 uncovered (0.6 of the random-model
mu). The largest valid (7,6) Haar graphs are at N = 2,352 (4,704 vertices), reached by self-dual sets and by k = 3
orbits alike, i.e. at the counting ceiling. c4 found a structural reason order-6 psi fail (an order-6 map on Z_n
confines the 1- and 2-orbits to a subgroup). Kept: nothing for the target; c3's orbit k = 3 and c2's plain/self-dual
tie went into my frontier runs (N 2,448-2,688). Honest note: the squad confirmed the counting argument across
seven families in 15 minutes; no idea beat random by more than the usual factor 0.6.
