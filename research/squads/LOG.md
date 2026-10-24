# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 19:00–19:30 UTC, cell-15-7 (Opus, cloud session), round 1 (c157-r1): more freed flags at (15,7)

Goal: beat the (15,7) table value 2,480,184 = 7·|H(11)|. Before the round (Opus alone, 18:15–19:00): the exp2-squad hub
trick carries over to 7 copies of H(11) with all three cross bijections equal (6 hubs per freed flag instead of 2);
K = 1 gave 2,480,190 (full symmetric BFS VALID), K = 8 gave **2,480,232** (freed sources and hubs BFS OK, k = 1, 2, 3).
Region-matched and Hopcroft–Karp cover installations (research/d15D7/regions.c, cover_match.c) replaced the greedy one
(start cost 3,410 vs 131,891 at K = 8). The bottleneck for larger K is cover conflicts. Brief: research/squads/c157-r1/COMMON.md.

Cards: c1 random-restart placement · c2 greedy placement by signature deficit · c3 annealing over flag sets ·
c4 hub-graph designs for K = 9..56 · c5 faster finishing local search · c6 better matching (exact candidates, Hall
violations) · c7 route-chart lift (5 letters × F_3, fibre F_3^6), a different construction · c8 wildcard (other ways to add
vertices).

Best per card: c1 leftover cost 32,205 at K = 24 (seeds move it only ~2 %) · c2 28,626 (−13 %) · c3 (see below) ·
c4 designs for every K = 9..51 (cyclic difference covers), K = 57 = PG(2,7), K = 56 impossible (det parity), K ≥ 58
impossible (counting) · c5 proxy 69,361 vs 75,606 after 600 s at K = 24 (−8 %) · c6 exact candidates: true Hall
deficiency 12,918 at K = 24 (8,496 points in ≥ 3 covers have no compatible line at all), leftover cost 20,037 (−39 %);
at K = 20 9,027 (−35 %), at K = 16 3,403 · c7 best chart 67 % nonsingular NB-6 patterns, largest perfect controller
PSL(2,11) m = 660 → a valid (15,7) graph of 962,280 vertices; groups of order ≥ 1008 miss elements; m ≥ 1702 is out of
reach (negative, as estimated) · c8 per-direction freeing: no gain (same 7 edges per 2 hubs; covers are the bottleneck).

Kept: c6's exact matching (cover_match2) for the K = 16 and K = 20 starts, c4's hub graphs (any K ≤ 51), c2 as a
small placement gain. Opus meanwhile: the exact covers of two flags overlap by 0 (chain position), 1,210/1,210 (generic,
balanced) or 1,210/1,331 (collinear points, unbalanced); triples overlap by ~100 ± 10 with random imbalance, which is
where the deficits come from (≈ 10 per triple), so K is limited to about 20 in this session.
