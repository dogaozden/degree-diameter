# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-26, big-squad-4-8, round 1 (goal: bipartite (4,8) > 2,184)

Session: Opus director, cloud (session_01QhUN8cKzD3kdiZv1fBP88r), branch claude/bipartite-4-8-squad-zmk3qt. Files:
research/squads/b48/ (tools/, r1/HEADER.md, r1/cards.md, r1/scoreboard.jsonl, r1/c01..c48/).
48 Haiku cards, 04:28-04:58 UTC. The environment allows 20 concurrent subagents, so the round ran as a rolling queue
(20 at a time, the next card launched as each finished); Haikus took 3-10 min each. Load peaked near 19 on 4 cores.
Director prep: built score48 (edge-list scorer), lift (voltage-lift annealer over any group table, batch eval mode),
groups.py; scanned 350 metacyclic Haar groups of order 1,092-1,120 with haar_fast (Z_91 x|_25 Z_12 reaches 2,184 = table).

Cards (one line each; best n / tool cost / miss = cost per vertex):
- c01 cost-1 wall at order 1,100: 2,200 / 1 (one B-side element at distance 9, no cost-0 neighbour). c02 k=20 family: 2,200 / 1.
- c03 k in {6,12,24}: 2,232 / 14. c04 k in {8,16,32,9,18,27,36}: 2,286 / 14. c05 prime k: 2,408 / 10. c06 non-faithful: 2,280 / 11.
- c07 scan rule (ord r >= 6, gcd(r-1,m) <= 2): 2,280 / 9 (meta 95 12 7). c08 two-level j-balance: 2,200 / 10.
- c09 orbit S under order-3 automorphism: 2,410 / 194. c10 order-2/4 symmetric S: not reported in time.
- c11 haar_sym ORBIT 3 1 1: 2,352 / 27. c12 PSL/SL/PGL x Z_n: 2,352 / 9 (psl 7 x 7). c13 AGL(1,q) x Z_n: 2,184 / 7.
- c14 Z_p^2 x| Z_k (lift): 2,366 / 12 (Z_13^2 x| Z_7). c15 products of non-abelian groups: 2,232 / 128.
- c16 orders 1,152 and 1,200: 2,400 / 17. c17 permutation groups: 2,304 / 32.
- c18 2+2 bases, metacyclic: 2,200 / 10 (miss 2.5, Z_55 x| Z_10). c19 2+2 non-metacyclic: 2,200 / 38. c20 3+3 bases: 2,304 / 64.
- c21 4+4 bases: 2,208 / 106. c22 abelian lifts, random bases: 2,190 / 108. c23 PG(2,3) lifts: 2,210 / 354.
- c24 GQ(3,3) lifts: 2,240 / 1,331. c25 girth-6 bases: 2,240 / 548. c26 small-diameter bases x small groups: 2,240 / 1,606.
- c27 big base x Z_4: 2,240 / 10,346. c28 bipartite Cayley, metacyclic: 2,340 / 100. c29 Cayley with involutions: 2,352 / 23.
- c30 canonical double covers: 2,200 / 2. c31 grow the 2,184 seed by 2 vertices: **2,186 / 247 far pairs (miss 0.23)**.
- c32 coset graphs: 2,448 / 28 (PGL(2,17)). c33 bi-Cayley with loops: 2,200 / 2. c34 better annealer: not reported in time.
- c35 GA over S: 2,200 / 2. c36 exhaustive Z_55-parts per j-pattern: 2,200 / 10. c37 affine maps (wildcard): 2,200 / 16,900.
- c38 Heisenberg(11) (wildcard): 2,662 / 200 (hard floor). c39 plain graph SA (wildcard): 2,186 / 25,471.
- c40 PG(6,3) line sets: 2,186 / 26,357. c41 non-bipartite bases + parity: 2,190 / 54. c42 triangular groups: 2,200 / 19.
- c43 learn from (4,7): 2,192 / 8. c44 Z_m x| Q non-cyclic Q: 2,286 / 370. c45 small group x big cyclic: 2,226 / 86.
- c46 near-miss anatomy: girth >= 8 already, waste is pigeonhole at lengths 7-8. c47 girth-8 restricted: 2,200 / 2.
- c48 graph SA (wildcard): 2,186 / 24,349.

Best: no valid graph. Lowest miss per vertex: c31 (surgery on the valid 2,184 seed, far pairs local). Lift near misses spread
their far pairs over every vertex by symmetry (n=2,200 cost 1 = 1,100 far pairs). Seven cards independently hit the same
Z_55 x|_2 Z_20 trap at cost 1.
Director, during the round: added haar_tab (haar_fast with any group table) and abc.py (split abelian-by-cyclic groups
M x| Z_k, M a sum of finite fields; metacyclic is the case f = 1). Z_13^2 x| Z_7 with haar_tab: cost 6 at n = 2,366 on 3
seeds (a hard floor, like cost 1 at 1,100).
Kept for round 2: (1) surgery on valid seeds (c31) with robust seeds; (2) abelian-by-cyclic groups beyond metacyclic;
(3) the order-1,100 trap only as a side line.
