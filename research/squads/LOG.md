# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24, cell-13-7 (Opus, cloud session), round 1: largest partial ovoid of Q(6,11)

Goal: (13,7), table 1,062,936 = 3 copies of the H(11) incidence graph + one matching. Opus found before the round
that the matching can be any bijection σ, and that removing the matching edges at a set R of pairwise opposite points
where σ is a local duality frees 6|R| slots for 2|R| new vertices (research/d13D7/REPORT.md, tri.c; greedy R ≈ 100
gave 1,063,140). Opposite points of H(11) are the non-orthogonal points of Q(6,11), so the round asked for the
largest partial ovoid of Q(6,11) (scorer research/d13D7/tools/oppcheck). Baselines: greedy ~100, elliptic 3-space
section 122, Opus ILS 133. Brief: research/squads/d13D7_r1/BRIEF.md.

Cards: c1 stronger ILS (tabu, plateau swaps) from the 133-set · c2 fixed-k penalty annealing · c3 union of parallel
affine lines (fibration), reduced to a clique in a class graph on F_11^4 · c4 unions of orbits of cyclic subgroups
of O(7,11) · c5 LNS with exact MIS repair · c6 pieces of elliptic sections + ILS · c7 wildcard · c8 theory-first
algebraic sets (polynomial graphs, repair).

Best per card (all re-checked by Opus with oppcheck; the top ones also with an independent numpy check):
c1 137 · c2 136 · c3 **243** (22 lines + e4, Python tabu) · c4 256 (orbits of an order-61 element, from its
results file; card did not report) · c5 134 · c6 282 (ILS seeded with a 136-set from 16 pooled elliptic sections) ·
c7 174 (min-degree greedy; not reported) · c8 **320** (took the same line-cylinder idea as c3 independently and
used a C clique search: 29 lines + e4).

Kept: the fibration (c3, c8): R = e4 + k conics through e4 whose planes share a tangent line, k = a clique in the
strongly regular graph Cay(F_11^4, {c^2 - 2a^2 - bf non-square}) (Delsarte bound 102). 320 points give 1,063,576
vertices (built by research/d13D7/build_d13D7.py; full all-pairs check running). Lesson: every structured method
(fibration, orbits, seeded ILS, min-degree greedy) beat the random-start local searches (133-137) by 1.3-2.4x.
Next: round 2 on the clique number of that graph (each clique vertex = 22 graph vertices).

## 2026-10-24, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH, resumed job), round 2: beat 320 pairwise-opposite points of H(11)

Goal: (13,7); the record graph is 1,062,936 + 2|R| with R a partial ovoid of Q(6,11) (pairwise opposite points of H(11)).
Start: |R| = 320 (round 1), whose graph 1,063,576 this session checked all-pairs (VALID). Brief:
research/squads/d13D7_r2/BRIEF.md (explicit coset graph Cay(F_11^4, {s^2+3c^2+8bf non-square}), lifter fiblift.py,
scorer oppcheck; c8 scorer linestar_check). Launched 22:28 UTC, 8 Haiku cards.

Cards: c1 DLS-MC max-clique in the coset graph · c2 other fibrations (square-class direction, multi-direction) · c3
fixed-k tabu for a 30-clique · c4 unions of orbits of cyclic subgroups of O(7,11) · c5 cliques invariant under small
similitude groups · c6 LNS with exact repair seeded from the 320 set · c7 wildcard (annealing on the affine model) ·
c8 line-stars (the line side of a relaxed surgery with distance-4 "stars").

Best per card (Opus re-checked the top ones with oppcheck and a numpy check): c1 29-clique = 320 (39,089 distinct
29-cliques, never 30; from its log) · c2 320 (square class only 20 lines; tangent direction pairs give nothing) ·
c3 320 · c4 **364** (orbits of an element of order 44; 55 -> 362, 110 -> 340) · c5 320 · c6 **397** (removing e4 frees
the 90 points at infinity blocked only by e4, 62 of them pairwise opposite: 381; LNS then 397) · c7 319 · c8 128 lines
in 121 stars (far below 320).

Kept: LNS (c6) and orbit unions (c4). 397 points give **(13,7) 1,063,730**, built by build_d13D7.py and checked
all-pairs by Opus (apsp_wide, VALID). c8 plus Opus's coherence test (relax/cohere*.c: for lines the "forbidden"
choices across a star are incoherent, for points they are coherent through the GQ Q(4,q)) close the star relaxation
for q = 11. The clique number of the coset graph looks like 29. Lesson: the structured record was not 1-swap optimal;
the exact-repair LNS found the swap that the clique searches could not see.
Side results the same evening, using the same theorem at other q (Opus, not the squad): (11,7) 400,040 (ovoid of
Q(6,9)), then 406,298 (explicit duality of H(9)); (9,7) 117,992; (7,7) 23,552.
Next: round 3 on beating 397 (LNS variants, deeper orbits, crossover, ARW, region blocks, fibration + infinity).

## 2026-10-24, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), round 3: beat 397

Goal: more pairwise-opposite points of H(11) than 397 (the r2 LNS plateau). Brief research/squads/d13D7_r3/BRIEF.md
(seeds: 397 from LNS, 364 from orbit unions). Launched 23:03 UTC, 8 Haiku cards.

Cards: c1 LNS continued (two-hub blocks, exhaustive (1,k) sweeps) · c2 LNS seeded with the 364 orbit set · c3 deeper
orbit unions (orders 44-220, commuting pairs, strong exact clique search, generators saved) · c4 crossover of good sets
+ LNS repair · c5 ARW-style tabu ILS · c6 LNS with geometric region blocks · c7 fibration cliques + points at infinity
jointly · c8 wildcard (penalty annealing, fibre exchanges).

Best per card: c1 397 · c2 364 (the orbit set is LNS-rigid) · c3 **720** (union of orbits of <a,b> = Z15 x Z5, a on a
5-dim U, b on U^perp; exact optimum of that group's orbit graph; cyclic groups of orders 44-220 peaked at 364) · c4 397
· c5 397 · c6 397 (still running at the time of logging) · c7 397 (score 11|K| + 122 - cov(K); 397 = 25 fibres + all
122 points at infinity) · c8 397 (locally optimal for every exchange of <= 5 fibres, 1,026,145 checked).

Verified by Opus: 720 (oppcheck BFS and numpy) -> (13,7) graph 1,064,376 (all-pairs check running at logging time).
Kept: orbit unions under small abelian groups with exact max-weight clique. Dropped: point-level LNS (all of
c1, c4-c8 converge to the same 397 basin; c3 showed 397 itself is a union of orbits of an order-11 Eichler element).
Lesson: the jump came from changing the symmetry class searched, not from more local search; Opus stopped the
LNS cards early (CPU needed for graph checks) once 720 was verified.
Next: round 4 (4 cards): orbit unions beyond 720 at q = 11, and the same method at q = 13, 7, 5 for the other
hexagon cells ((16,7), (9,7), (7,7)), plus LNS from 720.

## 2026-10-24/25, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), round 4: orbit unions at q = 11, 13, 7, 5

Goal: evolve round 3's winner (orbit unions + exact orbit-graph clique) and carry it to the other hexagon cells:
q = 11 (beat 720; (13,7), (14,7), (15,7)), q = 13 ((16,7)), q = 7, 5 ((9,7), (7,7)). Brief
research/squads/d13D7_r4/BRIEF.md. Launched 23:38 UTC with 4 cards only (the brief's "about 4 heavy runs at once";
Opus's graph checks needed the CPU).

Cards and best (verified by Opus with oppcheck): c1 q = 11 new group shapes: **756** (the order-15 subgroup <a b^2> of
round 3's Z15 x Z5) · c2 q = 13: **500** (was 168; cyclic group of order 30; commuting pairs <= 434) · c3 q = 7: **288**
(was 172; cyclic order 9, exact) and q = 5: **72** (was 58; cyclic order 18, exact); both plateau over hundreds of
groups · c4 LNS and orbit-level refills from 720: none (720 is locally rigid: no outside point blocked by fewer than
45 set points).
Kept / used: 756 -> (13,7) 1,064,448, (14,7) 1,774,584, (15,7) 2,484,720; 500 -> (16,7) 4,024,340; 288 -> (9,7)
118,224 (VALID); 72 -> (7,7) 23,580 (VALID). Lesson: the orbit method transfers unchanged between fields and gives
1.5-3x the plain local search at every q; smaller groups (bigger orbit graphs) did better than the larger group.

## 2026-10-25, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), round 5: orbit unions in GF(8) and in H(9)

Goal: carry the orbit-union method to the two cells it had not reached: (10,7) (pairwise-opposite points of H(8),
needs GF(8) arithmetic and characteristic-2 transvections) and (11,7) (pairwise non-collinear points of H(9), with
collineations built from the explicit duality and Frobenius). Brief research/squads/d13D7_r5/BRIEF.md. 2 cards,
launched 00:07 UTC (Opus's large graph checks needed the rest of the machine).

c1 q = 8: **217** pairwise-opposite points (was 84 by local search; 43 orbits of size 5 + 2 fixed points of an element
of order 5; 217 recurs in 6 groups) -> (10,7) 225,128, all-pairs VALID. c2 q = 9: **3,958** non-collinear points (was
3,859; checked by Opus with tools/ncolcheck.py) -> (11,7) 406,496 (all-pairs check running at logging time).
Lesson: the same method transferred to characteristic 2 and to a collinearity (not orthogonality) constraint with
little change; gains there are smaller (+2.6x at q = 8, +2.6% for the non-collinear sets, where local search was
already strong).

## 2026-10-25, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), round 6: beyond 756 at q = 11?

Goal: more than 756 pairwise-opposite points of H(11) ((13,7) +2, (14,7) +4, (15,7) +6 per point). Brief
research/squads/d13D7_r6/BRIEF.md; 3 cards, launched 00:47 UTC (the (16,7) check needed the rest of the machine).

c1 non-abelian groups (closure <= 2000): **756** again, a different set (block group of order 72, exact optimum);
order 360 and 600 groups give 720 · c2 warm starts: tabu from the 756 clique on the orbit graphs of the subgroups of
order 5 (K = 29,540) and 3 (K = 60,028) finds nothing heavier; the normaliser of <h> (order 19,200) and 19 overgroups
<h, g>: max 756 (another different set) · c3 new block shapes (4+3, 3+2+2): exact optima 720 for orders 45 and 75.
All re-checked by Opus (oppcheck). Result: no gain; 756 is reached by three unrelated group families and is the exact
optimum of every orbit graph tried that contains it, so it looks like the ceiling of this method at q = 11.

## 2026-10-25, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), late results from rounds 2, 3 and 5

Round 5 c2 kept working after its first report: a seeded point ILS (ncol_seed.c) from its 3,958 orbit union reached
**3,967** pairwise non-collinear points of H(9) (checked by Opus with tools/ncolcheck.py) -> (11,7) 406,514, full
all-pairs VALID (research/d13D7/checks/d11D7_hex9_dual_R3967_n406514.check.txt). The 406,496 graph from the 3,958 set
was all-pairs VALID as well. Its warm-started orbit clique for <delta^2> alone reached orbit weight 3,964 (not used).
Round 2 c7 (fiber-line model, 320) and round 3 c6 (geometric LNS blocks, 397) appended their final lines late; no
gain. Round 2 c1 was still running a clique search hours after its round closed; Opus stopped it.

## 2026-10-25, cell-13-7 (Opus, cloud session_0136phW63ksffo3wvN1THJtH), round 7: more points of H(13) for (16,7)

Goal: more than 500 pairwise-opposite points of H(13) (+4 vertices each at (16,7); q = 13 had had one card, round 4 c2,
against three rounds at q = 11). Brief research/squads/d13D7_r7/BRIEF.md; 4 cards (one core each), 25-minute box,
launched 01:59 UTC.

c3 non-abelian groups (port of round 6's nonab.py): **792** (oppcheck VALID), the union of 7 orbits of a monomial group
of order 1296 on the three hyperbolic planes (two generators of order 18; exact optimum of its orbit graph; the same
792 also from another order-1296 group and an order-324 group). Per family: monomial 792, frame 604, block 424,
decomposition 416, dihedral 396 · c1 warm-started subgroup tabu: 536 from the order-30 group of the 500 set; redirected
by Opus to subgroups of c3's group, no gain over 792 (orders 162, 108, 81, 54 exact) · c2 block pairs from q - 1 = 12
and q + 1 = 14: best 494 (a of order 12 on dim 5, b of order 3) · c4 point-level tabu/ILS from the 500 set: no gain;
every point outside it conflicts with at least 20 members, so point moves cannot extend such orbit unions.
Opus re-checked 792 with oppcheck and rebuilt (16,7): 4,025,508 = 5 * 804,468 + 4 * 792, VALID from all level-0
vertices and hubs (research/d13D7/checks/d16D7_hex13_R792_n4025508.check.txt; +3,168 over the table, was +2,000). The same monomial family gave only 720 at q = 11 in round 6; Opus re-ran it at q = 11 with a larger closure cap
(research/squads/d13D7_r7/opus_q11mono/, 56 groups): 720 again, the exact optimum for five different groups, so it
does not carry over to (13,7). Structure of the 792 set: with x3 = 1 the products (x0x4, x1x5, x2x6) are a
permutation of (0,0,1), (3,12,12), (3,3,8) or (9,9,9), and in each class (x0, x1, x2) is a union of cosets of mu_3^3.
