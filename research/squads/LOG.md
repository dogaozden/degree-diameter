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
A6 20, A5 x C7 16, order 363-366 groups 10-16 · c4 no union passes X X = G on 686_1/3/5 · c5 10 (688, Z43:Z4) · c6 16
(756, 378_41; 97 groups of order 361-400) · c7 27 (728, PSL(2,13)), 49 (880, PGL(2,11)) · c8 6 (686), 98 (722);
metacyclic bipartite Cayley graphs at K = 6 exist at 400 and 500 vertices (12/104, 15/65 groups) and die out before 600.
Kept / learned: no family gets near 0 above 700 vertices; the self-dual sweep's closest misses are at 696-704
(351_12: 4, 352_50: 1). (6,5) at > 684 looks out of reach for Haar-type and bi-coset constructions of this size.
What next (director): keep the sdk sweep of 361-450 running on 2 cores; move 2 cores to (9,5), where the director's
new tabu (src/sdtabu.c) finds valid self-dual 9-sets on C197 : C7 (order 1379, the group of our 2,758 record) in
10-40 s, so orders above 1379 look reachable.
Outcome of the job (director, 03:00 UTC): no further squad round. The two (6,5) cores went on with the sdk sweep
(nothing above 684; closest still 352_50 at 1); (9,5) went from 2,758 to 3,036 in nine verified steps (1395 ... 1518),
five of them from 300 s deep tabu runs on near misses (research/selfdual-d5/README.md).

## 2026-10-31, job selfdual-d5b, round sd5b-r1 (04:33-05:40 UTC), goal (9,5) > 3,036

Context: the director's self-dual tabu (research/selfdual-d5/src/sdtabu2, K = 9) was sweeping metacyclic groups of
order 1519-1650, affine F_p^d : C_k and SmallGroups of order 1520-1560 with a normal C_p (best 4 so far); near misses
above 1518 were SmallGroup(1539,31) and (1539,45) at 2. Rules `sd5b-r1/COMMON.md`, cards `sd5b-r1/CARDS.md`,
scoreboard `sd5b-r1/scoreboard.jsonl`. Cards: c1 SmallGroups 1561-1640 with a normal C_p acting with order >= 3 ·
c2 non-metacyclic direct products · c3 C_m : H, m composite, H non-cyclic · c4 affine F_p^2 : H, H non-cyclic ·
c5 simulated annealing in place of tabu · c6 two-item moves / elite restarts · c7 non-solvable groups · c8 wildcard
(it chose plain, not self-dual, Haar tabu with a BFS energy).
Best per card (energy |G \ X X|, 0 = valid; nothing valid, no card claimed one): c1 12 (SmallGroup(1596,3), 11 of 54
candidates screened) · c2 19 ((C7:C3 x C13:C3) x C2, 1638) · c3 23 (C195 : Q8, 1560) · c4 **2** (F13^2 : (C3 x C3)
diagonal = (C13 : C3) x (C13 : C3), order 1521, record 3 type (3,3); 100 s stayed at 2) · c5 2 on the 1539 near misses
(calibration: annealing finds 5-6 solutions per 45 s on C197 : C7 where tabu finds 15, so weaker) · c6 no run at
>= 1519 (calibration on C197 : C7, 30 s: tabu 10, elite restarts 12, two-item moves 7) · c7 14 (C3 x C9 x A5, 1620;
non-solvable groups 14-31) · c8 26 (plain Haar, C73 : C21, 1533; not comparable).
Kept / learned: (C13 : C3)^2 is a new near miss (2) outside the director's lists; the other families are far (12+);
annealing and compound moves do not beat the tabu. What next (director): deep tabu (900 s, endgame scan) on
(C13 : C3)^2 stayed at 2, so the near misses (1539_31, 1539_45, 1525_1, (C13 : C3)^2, ...) go to EXHAUSTIVE sdk
enumeration of their types (about 1e9 sets per record and type at these orders, minutes each).
