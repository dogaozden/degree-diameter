# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-31, handsoff-37 round 1 (Opus coordinator, hands-off; Haikus do the work)

Session claude/handsoff-37-d3d7-r13gzx, goal: bipartite (3,7) above 168. 8 Haiku workers, 15:44-17:36Z, about 1h35-1h50
each, cards in research/squads/handsoff-37/cards.md, scoreboard research/squads/handsoff-37/scoreboard.tsv.
- c1 surgery on C168.1 (exhaustive 2-/3-edge pair insertion + tabu): 170 far 46; 172: 80, 174: 107, 176: 122.
- c2 shrink n=180 near misses (beam of pair reductions + SA, restarts): 170 far 70; 176: 86; no gain at 180 / 192.
- c3 Z7 / Z5 lifts by randomized exact DFS and SAT (cadical, kissat): did not even recover the known Z7 12+12 lift at 168.
- c4 joint base + voltage tabu over small groups: 168 over C14 in 14 s; 192 (C8, 12+12) far 272 (old best 384); 182: 168.
- c5 order-3 automorphisms with fixed vertices (quotient SA): 170 far 78.
- c6 polarity double covers with a free Z_t on M: diameter 7 at 140, 150, 160 (easy); 170 far 80, 172 far 76.
- c7 unstructured parallel tempering: calib 150 far 19, 160 far 53; 170 far 46 (same basin as c1).
- c8 wildcard, LNS with exact re-matching + Tutte 12-cage growth: 170 far 46 (same basin), cage growth far 170.
Best: n = 170 far 46 (one basin reached by c1, c7, c8). No candidate. Kept: other seeds (r2a), exact region repair
(r2b), polarity covers (r2c), lift tabu with plateau escape (r2e); new: Moore-tree completion (r2d), mixed free / non-free
symmetry + exact search (r2f), wildcard (r2g), n = 169 (r2h).

## 2026-10-31, handsoff-37 rounds 2 and 3 (hands-off coordinator)

Round 2 (17:25-19:40Z, 8 Haikus; r2a, r2b, r2d stopped early): r2a other 160-168 seeds (stopped, no notes); r2b exact SAT
region repair (radius 2: far 46 is a local optimum; radius 3-4 too slow); r2c polarity covers deeper (Z5 floor far 80 at
170, exact 5-/6-subset re-solves find nothing lower); r2d Moore-tree / involution (nothing below 46); r2e breakout lift tabu
(182 far 126, 190 far 220); r2f non-free F21 symmetry (168 rebuilt in 3 s from scratch; 182 far 210, 196 far 224); r2g
non-free colour-preserving orbit search (170 far 165); r2h n = 169 with a fixed radius-6 tree (far 144).
Kept: the F21 lead (r3a, r3b), breakout (r3c, r3e, r3f), polarity (r3d, r3g).
Round 3 (18:20-21:15Z, 7 Haikus): r3a non-free symmetric SA (170 D5 far 60; 180 far 180); r3b breakout in the symmetric
search (D5 floor 60); r3c breakout lift tabu (170 C5 far 65; rediscovered the 180 far-36 near miss as an S3 15+15 lift);
r3d D5 polarity (170 far 130); r3e breakout on the far-46 basin (cannot escape; own best 59); r3f breakout at the near
misses (192 far 256, old 384); r3g Z5 orbit insertion into 160 covers (170 far 70).
Result: no record; best 170 far 46. Spend: Opus 0.478 / Haiku 0.927 units (66% Haiku). REPORT:
research/squads/handsoff-37/REPORT.md.
