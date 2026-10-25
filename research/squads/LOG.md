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

## 2026-10-24 19:32–20:00 UTC, cell-15-7 (Opus, cloud session), round 2 (c157-r2): finishing the tail, verification

Goal: more freed flags at (15,7) (each +6 vertices) and independent checks. Before the round Opus had K = 16 starts
from round 1's exact matching (c6) and found that the real 7-copy graph needs far fewer repairs than the search proxy
(K = 16 checkpoint at proxy ≈ 35: 3 far pairs, the next one 0). During the round: **K = 16 → 2,480,280** (valid,
filed). Brief: research/squads/c157-r2/COMMON.md.

Cards: c1 ejection-chain tail finisher · c2 parameter sweep of the finishing search (BESTK, T0) · c3 flag placement by
Hall-violation counts · c4 lemma validation on small hexagons (kcopy_hub check vs apsp.c vs apsp_sym.c) · c5 an
independent edge-list builder (Python, from the description only) · c6 wildcard (three different cross bijections, or
hubs with fewer attachments).

Best per card: c1 (see below) · c2 (see below) · c3 worse than random (K = 24 leftover 26,403 vs 20,037) ·
c4 72/72 cases agree, lemma holds in all (22 valid, 25 degree-invalid, 25 distance-invalid) · c5 edge set identical to
kcopy_hub's for K = 8 (sha256 b9e54f48…) · c6 different bijections: new routes cover only ~6 % of the far pairs
(10 % at K = 20); hubs missing a copy reach ~9 % of it, so 6 per flag stands.

Kept: c4 and c5 as the verification of the final graph (c5's builder + apsp_sym.c, independent of kcopy_hub.c).

## 2026-10-25 10:40–11:25 UTC, cell-15-7 resume (Opus, session_01P3FWCNGZp2xTc6sYGPNtj4), round 1 (c157b-r1)

Goal: (15,7), branch record 2,500,147 = 14·177,156 + (R_H + 1,536) + (R_L + 1,536) (typed levels + mirrored surgery,
unequal hub sides, Opus before the round). Every lever was put to the squad: R_H (non-collinear points of H(11), 8,645,
+1 each), R_L (non-concurrent lines, 8,246, +1 each), m (mirrored set, 768, +4 each). Scorer: chkset.py / chkmirror.py.
Brief: research/squads/c157b-r1/COMMON.md, CARDS.md.

Cards: c1 plain ILS engineering (points) · c2 orbit ILS under the order-7 / order-19 subgroups of the order-133 group
(points) · c3 the same for lines · c4 orbit searches under other groups (points) · c5 the same for lines · c6 k-fixed tabu
(points) · c7 mirrored sets beyond 768 · c8 wildcard (algebraic sets, König merges, hyperplane sections).

Best per card: c1 8,645 (no gain; exact region re-solves around RH find no +1; from random 7,629) · c2 8,645 (no gain;
from scratch 7,889 / 7,961) · c3 8,246 (no gain) · c4 8,645 (Singer normaliser G399 gives another 8,645 set meeting RH in
6,783 points; other groups 7,432–8,183) · c5 8,163 (C110; no gain) · c6 none feasible at K = 8,646 (penalty 1) · c7 768
(pairwise-opposite mirrored sets = partial ovoids of H(11), the 756 base is rigid) · c8 8,645 (König merges gain 0;
hyperplane sections ≤ 1,596).

Kept: nothing from the plain-set searches (8,645 / 8,246 look like the cap for these methods; RH is invariant under the
order-399 normaliser). Opus meanwhile: a relaxed surgery theorem (research/d15D7b/RELAXED.md) that allows collinear pairs
in the friendly sets when the hubs of each paired element are wired to freed elements incident with its partner; with it
the four bottleneck sets grow to ~9,000 points / ~8,600 lines: (15,7) 2,500,749, then 2,501,008 (BFS-checked).

## 2026-10-25 12:05–12:45 UTC, cell-15-7 resume (Opus, session_01P3FWCNGZp2xTc6sYGPNtj4), round 2 (c157b-r2)

Goal: raise the relaxed construction (branch record 2,501,008; the stock scorer re-scores those sets to 2,500,999 because
its cover design is randomised). Scorer: research/d15D7b/score_relaxed.py (four bottleneck sets -> covers, hub
assignment, drops -> n). Brief: research/squads/c157b-r2/COMMON.md, CARDS.md. Five cards (c3 = Opus's own alternating
runs), one process each.

Cards: c1 a stronger ILS for the point sets · c2 the same for the line sets · c4 fewer drops in the assignment ·
c5 other starting sets · c6 wildcard (interlocking coverage).

Best per card: c1 2,501,023 (pils.c: raw sets grow to 9,177 / 9,171 but drops rise to 191) · c2 2,501,002 (pair-free
additions only; free pairs raise S3 to 9,156 raw but 909 drops) · **c4 2,501,016 with 0 drops: design3.py gives every
needed partner a private covering element (no covering element holds two needed elements, and the joining line of a
pair is never a cover)** · c5 2,500,999 (all six alternative starts score lower: drops 467-583) · c6 2,500,999 (notes
the overlaps P0 ∩ P1 = 563, S3 ∩ S4 = 471 waste coverage) · Opus c3 (10-minute alternating runs) 2,501,057, with
c4's design3 2,501,077.

Kept: c4's design3.py (in the final scorer), Opus's alternating runs. Lesson: pairs pay only when their coverage is
uncontested; the searches that ignore the assignment grow raw sets but lose it in drops.
