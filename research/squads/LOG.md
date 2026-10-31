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
