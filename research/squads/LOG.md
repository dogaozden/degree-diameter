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

## 2026-10-26, big-squad-4-8, round 2 (goal: bipartite (4,8) > 2,184)

26 Haiku cards, 04:59-05:17 UTC, 20 at a time (folder research/squads/b48/r2/). Selection from round 1: 12 cards on split
abelian-by-cyclic groups (the director's new family), 9 on surgery of the valid 2,184 seed (c31's line), 3 side lines,
2 wildcards. New tools: haar_tab, abc.py, farlist, edgecrit, flift (fast multi-fibre lifts, ~140k evals/s on 2+2 bases).
Best per card (n / cost; surgery cards report far pairs):
- a01 1,120 group root variants: all isomorphic, 2,240 / 3. a02 char-2 components: 2,240 / 3. a03 Frobenius Z_p^m x| Z_d:
  2,352 / 4 (Z_7^2 x| Z_24). a04 d = 1, 2 components: 2,200 / 7. a05 diagonal actions: 2,200 / 1 (the known trap).
- a06 floors: uncovered elements are reached by ~30 walks of length 9 and none of length <= 7; no rule found.
- a07 three components: 2,352 / 26. a08 orders 1,296-1,444: 2,664 / 26. a09 abc groups on 2+2 bases: 2,200 / 38.
- a10 single field, non-faithful: 2,400 / 6 (F_25 x| Z_48). a11 annealing settings: no gain (1,120 at 3, 1,176 at 4).
- a12 exhaustive kernel parts for 6 of 353 j-patterns of the 1,120 group: floor 6 (lift-style cost).
- b01 31 valid 2,184 seeds of Z_91 x|_25 Z_12, all with the same edge damage (165, 165, 180, 180): probably one graph;
  no other order-1,092 group reaches 0. b02 smart triples: 2,186 / 220. b03 gadget variants: 227. b04 repair c31: 247
  (strict local minimum). b05 triple geometry: 220 (single-replacement local optimum). b06 no valid Haar graph at
  N = 1,040-1,091 in short screens; damage does not fall with N. b07 local gadgets: 227. b08 annealed insertion choices:
  **2,186 / 217** (4 deleted edges, no x-y edge). b09 rewiring a generator class of the 1,100 near miss: no gain.
- c01 margin objective: same cost-1 state at 1,100. c02 2+2 lifts with flift: 2,200 / 22. c03 hard-set-first: floor 8
  (lift-style) on both leads. w1 non-split metacyclic: 2,200 / 4. w2 two-sided translations: no gain.
No valid graph. Director, after the round: an exhaustive search over all Haar graphs of a metacyclic group up to
automorphism (tools/exh_meta.py | flift eval; ~540k sets/s, 30 s per group of order 1,100) confirms Z_91 x|_25 Z_12
reaches 0 and proves Z_55 x|_2 Z_20 cannot (minimum = the cost-1 trap). The annealing floors are true minima.
Kept: (4,8) looks closed for Haar graphs of solvable groups near order 1,100 and for local surgery (floor ~217). Round 3
moves the main effort to (4,9) (table 4,970), where a director probe already found metacyclic Haar graphs at order 2,496
(n = 4,992) with cost 4, plus a few (4,8) cards.

## 2026-10-26, big-squad-4-8, round 3 (goal: (4,9) > 4,970, plus 4 cards on (4,8))

20 Haiku cards, 05:19-05:35 UTC (research/squads/b48/r3/). Moved to (4,9) after two (4,8) rounds, as the brief allows.
Director, before the round: 4,970 = 2 x 2,485 = Haar graph size of the Frobenius group Z_71 x| Z_35; a 10 s haar_fast probe of
64 metacyclic groups above it found cost 4 at order 2,496 and cost 2 at Z_101 x|_5 Z_25 (2,525, n = 5,050); the exhaustive
search over all 79.5 million Haar sets of Z_101 x| Z_25 (up to automorphism) gives minimum lift-cost 2: no valid graph.
Cards (best n / cost, (4,9) unless noted):
- d01 Frobenius Z_p x| Z_k: 5,306 / 10. d02 large k: 4,992 / 4 (meta 104 24 7, 3 seeds). d03 k 12..19: not reported in time.
  d04 k 6..11: 5,306 / 10. d05 exhaustive certification: one partial run (meta 421 6 21, minimum 685 so far).
- d06 abelian-by-cyclic: 5,256 / 10. d07 PSL/SL/PGL x Z_n: 5,040 / 7 (S5 x Z_21). d08 AGL(1,q) x Z_n: 5,060 / 14.
  d09 products: 5,040 / 9. d10 2+2 lifts: 5,020 / 24. d11 3+3 and 4+4 lifts: 5,022 / 36. d12 Cayley: 4,992 / 152.
- d13 involution rule at D = 9: in these groups many involutions did better, not worse (meta 89 28 34 192 vs 2,772).
- d14 orders 2,486..2,495 (no good metacyclic group): 4,984 / 192. d15 coset graphs (wildcard): 6,072 / 96.
- d16 analysis: in meta 104 24 7 the central involution (52, 0) is far in every cost-4 solution (a plateau, not one trap).
- (4,8) e01 exhaustive certification of 5 more groups: each minimum equals its annealing floor. e02 multi-fibre Frobenius
  lifts: 2,328 / 120. e03 more groups of order 1,152/1,200: 2,304 / 9. e04 nilpotent groups: 2,240 / 233.
No valid graph. Kept: nothing for (4,9) beyond the floors; the brief's next cells are (3,9) and (3,10). An earlier session
(claude/voltage-lifts-search-6lfotq) left a (3,10) exhaustive 2+2 scan unfinished at group order 208; round 4 picks it up.
