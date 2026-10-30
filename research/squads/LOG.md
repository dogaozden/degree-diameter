# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-30, job selfdual-d5, round sd5-r1 (21:17-21:50 UTC), goal (6,5) > 684

Context: the director's sdk.c (valency-K self-dual = bipartite Cayley Haar search, calibrated) was sweeping every
non-abelian group of order 343-450; best so far |G \ X X| = 1 at SmallGroup(352,50) (type (6,0), all of it searched),
most groups of order 361+ miss by 9 or more. Rules `sd5-r1/COMMON.md`, cards `sd5-r1/CARDS.md`, scoreboard
`sd5-r1/scoreboard.jsonl`. Cards: c1 order-4 self-duality (beta of order 4) · c2 tabu inside the self-dual family
(sampled (4,1)/(6,0) types) · c3 plain (not self-dual) Haar tabu · c4 bi-coset |H| = |K| = 2 · c5 2+2 voltage lifts ·
c6 order-3/5 automorphism-invariant Haar sets · c7 wildcard: bi-coset |H| = |K| = 3 · c8 wildcard: formula-only
metacyclic bipartite Cayley graphs (tabu on T directly), orders 2n = 600-722.
Best per card (no card found a graph above 684; every card calibrated on a known valid case, apsp-checked):
c1 8 (750, SmallGroup(375,5); 186 of 334 groups of order 363-400) · c2 20 (728, 364_1; re-finds cost 1 on 352_50, 0
on SL(2,7)) · c3 2 (720, SL(2,5) x C3 = 360_51, where an earlier exhaustive search says no Haar graph exists);
A6 20, A5 x C7 16, order 363-366 groups 10-16 · c4 no union passes X X = G on 686_1/3/5 · c5 11 (704, Z44:Z4) · c6 16
(756, 378_41; 97 groups of order 361-400) · c7 27 (728, PSL(2,13)), 49 (880, PGL(2,11)) · c8 6 (686), 98 (722);
metacyclic bipartite Cayley graphs at K = 6 exist at 400 and 500 vertices (12/104, 15/65 groups) and die out before 600.
Kept / learned: no family gets near 0 above 700 vertices; the self-dual sweep's closest misses are at 696-704
(351_12: 4, 352_50: 1). (6,5) at > 684 looks out of reach for Haar-type and bi-coset constructions of this size.
What next (director): keep the sdk sweep of 361-450 running on 2 cores; move 2 cores to (9,5), where the director's
new tabu (src/sdtabu.c) finds valid self-dual 9-sets on C197 : C7 (order 1379, the group of our 2,758 record) in
10-40 s, so orders above 1379 look reachable.
