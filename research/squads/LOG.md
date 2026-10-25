# Haiku squad log

One entry per squad round (see .claude/skills/haiku-squad/SKILL.md). Started Oct 23, 2026.


## 2026-10-24 18:55–19:30 UTC, cell-14-7 (Opus, cloud session), round 1 (16 cards, two squads of 8): (14,7)

Goal: beat (14,7) = 1,771,560 (Delorme–Gómez–Quisquater polygon cover: GH(11) + 2 matchings over Z5). Opus before the
round: built GH(q) (gh_build.c) and a lift annealer (glift.c); found that one copy past 2j+1 works at small q
(GH(2)+1 over Z4, 504, apsp VALID) but random matchings leave ~27,600 misses per source at q = 11 (Z6).
Brief: research/squads/d14D7-r1/BRIEF.md; cards research/squads/d14D7-r1/cards/; scoreboard scoreboard.jsonl.

Cards: c1 Weyl-distance building scan at D ≤ 7 · c2 literature · c3 GH(q) over GF(4), GF(8), GF(9) and the
GH(9)+4 / GH(8)+5 regime · c4 how many copies for GH(3)+2 · c5 targeted annealing for one matching over Z4 ·
c6 Singer-symmetric matchings · c7 route-chart lifts at D = 7 · c8 wildcard · c9 GH(11)+2 configurations over
order 6–8 · c10 GH(5)+2 over Z6 (→ (8,7)) · c11 GH(7)+2 over Z6 (→ (10,7)) · c12 counting bounds for extra copies ·
c13 Haar baseline at (14,7) · c14 polygon cover + extra vertices · c15 GH(13) with rewired matchings · c16 wildcard.

Best per card (valid unless noted): c1 none (A2–A5 scanned, rest unscanned; fixed a pruning bug) · c2 no newer
bipartite D = 7 record; general (14,7) = 6,200,460 (Gómez–Fiol–Serra compound on GH(11)) · c3 GH(4), GH(8), GH(9)
built; random misses/source GH(9)+4/Z14 6,031, GH(8)+5/Z24 5,290 (not valid) · c4 GH(3)+2 over Z6 = 4,368 (apsp
VALID), Z7 not reached · c9 best 8,006 misses/source (Z6, random polygon voltages; not valid) · c10 GH(5)+2/Z6 full
cost 253,776, annealing −4 % (not valid) · c12 counting does not exclude (11,2,m=6..8) · c14 **+60 vertices on
GH(3)+2 over Z5** (3,640 → 3,700, apsp VALID; delete base edges, attach new vertices; a Z5-symmetric unit of +2 is
valid alone) · c16 LPS Ramanujan Cayley graphs: (14,7) only 205,320 · c8 GQ lifts without matchings fail (girth) ·
c5, c6, c7, c11, c13, c15: no report before the round was closed or no valid improvement (see their folders).

Kept: c14's unit. Opus turned it into a construction with a proof: delete one matching edge (p, l) in all copies and
add z ~ {(p,c)}, z' ~ {(l,c)}; only the routes from (p,c) to points opposite p and from (l,c+h) to lines opposite l
break, and they are repaired exactly by prescribing sigma_t on the points at distance 4 from p (the 14,641 lines at
distance 4 from a line M through p, not projecting onto p, partition the opposite points). **Result: (14,7) 1,771,562
(one unit; ucheck12 over all sources VALID; apsp running).** The same construction beats every DGQ value: D = 5
(10,5)…(15,5) all apsp VALID, and (7,7) 23,438 apsp VALID (research/cell147/units/README.md).
Squad assessment: the round produced the decisive idea (c14). The other cards mostly confirmed negatives
(extra copies at large q, random-like constructions, buildings, LPS) — useful for the cell notes.

## 2026-10-24 22:41–23:10 UTC, cell-14-7 second session (Opus, cloud), round 2 (16 cards, two squads of 8): (14,7) packing and the other D = 7 cells

Opus before the round: found the TYPE-2 unit design (incident flag p ∈ l = sigma_t(p); sigma_t maps the 121 points
collinear with p off l onto the 121 lines meeting l off p; both unit endpoints then reach everything within 7), so a
unit costs 121 assignments instead of 14,641; units of one matching need disjoint zones (a packing problem); wrote
uhcheck (hub-aware checker), apsp_cyc (independent check on edge lists), t2design, pack, t2cell.sh. (14,7) 1,771,870 with
155 units (uhcheck over all sources VALID). Brief: research/squads/d14D7-r2/BRIEF.md; cards in cards/; scoreboard.jsonl.

Cards: c1 annealing schedules · c2 (1,2)-swap ILS · c3 least-blocking greedy · c4 algebraic partial ovoids (Tits chart)
· c5 automorphism orbits · c6 exact optimum at small q · c7 wildcard (other unit types) · c8 super-hubs · c9–c16 type-2
units in the cells (7,7), (9,7), (11,7), (12,7), (13,7), (15,7), (10,7) (new GF(8) hexagon), (16,7).

Best per card (flags per matching at q = 11 for c1–c5): c1 76 · c2 87 · c3 **91** · c4 78 (tabu finds 130 pairwise
opposite points, but choosing pairwise opposite flag lines for them stalls near 47) · c5 71 (1,200 monomial
automorphisms found; symmetric packings below random) · c6 q = 3 exact max 28 = an ovoid with its dual spread; q = 5
best 34 · c7 none · c8 no super-hub cover by <= Delta hubs · c9 (7,7) 23,496 (uhcheck + apsp_cyc VALID) · c10 (9,7)
117,742 (uhcheck + apsp_cyc VALID) · c11 (11,7) 398,702 (full uhcheck) · c12 (12,7) 664,544 (full uhcheck) · c13 (13,7)
1,063,098 (QUICK: unit endpoints + new vertices) · c14 (15,7) 2,480,670 (QUICK) · c15 (10,7) 224,798 (full uhcheck; Opus
apsp_cyc VALID) · c16 (16,7) 4,022,726 (QUICK).

Kept: c4/c6/c9's observation (pairwise opposite points AND pairwise opposite lines are conflict-free; c6's q = 3 optimum
is an ovoid + dual spread). Opus combined it with the Hermitian spread: the hexagon lines inside an elliptic hyperplane
section E of Q(6,q) (X4 = -X0 at q = 11) are 1,332 pairwise opposite lines partitioning E, so flags (p, spread line
through p) never conflict on the line side and the packing is a partial ovoid inside E (orthogonality graph on 15,984
points, degree 1,342): ILS finds 152 in 60 s (spreadpack.c) against 91 for the best card. Squad assessment: the cell
cards (c9–c16) turned the trick into new highs in all eight other DGQ D = 7 cells within one round; the packing cards
gave +15 % over random, and the structural hint that led to the spread construction (+67 %).

## 2026-10-24 23:20–00:10 UTC, cell-14-7 second session, round 3 (8 cards, one squad): partial ovoids inside E (q = 11)

Goal: more flags per matching than the Hermitian-spread packing (155 = a partial ovoid of the elliptic quadric E =
Q^-(5,11), X4 = -X0, found by local search). Brief: research/squads/d14D7-r3/BRIEF.md (graph E11.graph, map E11.map,
scorer pack CHECKONLY). Cards: c1 ARW ILS · c2 fixed-k tabu · c3 cyclic orbits of isometries of O^-(6,11) · c4 algebraic
seeds (elliptic 3-space sections) · c5 annealing · c6 GF(9) spread packings for (11,7), (12,7) · c7 q = 13 for (16,7)
· c8 wildcard (several elliptic sections).

Best per card: c2 159 (216 when seeded from Opus's set; no 217) · **c3 240** (60 orbits of an order-4 isometry; order 12
gave 204, order 6 210, order 3 162) · c4 169 · c8 155 (union of five sections, no gain) · c6 (12,7) 664,852 and (11,7)
398,852 (GF(9) spread, 136-138 flags per matching; full uhcheck) · c1, c5, c7: see below.

Opus: c3's order-12 idea solved exactly. E's space is A ⊥ V4 (A = (x0,x3) anisotropic, V4 = (x1,x2,x5,x6) hyperbolic);
the rotation orbits of order 12 correspond to points b of PG(3,11) off the quadric of V4, and two orbits are compatible
iff the line through them is a secant (B4^2 - 4Q4Q4' a nonzero square). Exhaustive branch and bound: maximum 17 orbits
(vertex-transitive graph), plus 12 fixed points = 216, maximal (secantclique.c). Phase-class refinements of the same
rotation (phaseils.c): order 4 gives 192, order 2 gives 207, so c3's better order-4 element must also move V4. Point-level
ILS seeded from 240 stays at 240. Opus also swept c3's 22 sampled isometries of orders 4, 8 and 10 with a C
orbit-clique search (orbitclique.c, 40 s each): an order-8 element also reaches 240 (30 orbits of 8); order 10 gives up to
228; the other order-4 elements give 179-216. Kept: 240 for (14,7) (1,772,520, full uhcheck VALID); same flags give
(13,7) 1,063,416 and (15,7) 2,481,624; orbit packing at q = 13 (17 rotation orbits of 14 + 14 fixed = 252) gives (16,7)
4,023,348. Squad assessment: the round's decisive contribution was c3's symmetry idea (+55 % over the best local search,
which plateaued near 155-169 on the raw graph); Opus turned it into an exact secant-graph construction and a fast sweep.

## 2026-10-25 00:36–01:10 UTC, cell-14-7 second session, round 4 (8 cards, one squad): structured partial ovoids

Goal: beat N = 240 points (flags per matching) at q = 11 and transfer the orbit method to the other D = 7 cells. Brief:
research/squads/d14D7-r4/BRIEF.md. Cards: c1 two-generator groups · c2 large-neighbourhood search around 240 · c3 product
groups rotation x (X,Y)-action on V4 · c4 q = 13 orbits (16,7) · c5 q = 5, 7 (7,7), (9,7) · c6 q = 9 orbits (11,7),
(12,7) · c7 GF(8) spread for (10,7) · c8 wildcard (Singer-type elements).

Best per card: c1 240 (cyclic order-8 group; 17 subgroup systems of 8 commuting pairs, none above) · c3 216 (no product
group above) · c8 240 (order-37/111 elements give no independent orbits; the 240 sets are rigid: no (1,2)-swap, and the
union of the two 240 sets has maximum independent set exactly 240) · **c4 280 at q = 13** (order-7 sub-rotation of the
anisotropic plane + 14 fixed points; (16,7) 4,023,460, quick check) · **c5 (9,7) 117,824** (88 flags from an order-4 power
of an order-8 isometry; uhcheck + apsp_cyc VALID; q = 5 stays 48) · **c7 (10,7) 224,946** (GF(8) elliptic section
X4 = X0 + X3, 513-line spread, 126 flags; full uhcheck; Opus apsp_cyc VALID) · c2, c6: see below.

Opus: q = 11 is stuck at 240 for every group tried (also the sub-rotations of sizes 6, 3: 216, 211). Following c4,
phaseils with sub-orbits of size 7 at q = 13 gives 294 (41 x 7 + 7 fixed): (16,7) 4,023,516 (quick check). Squad
assessment: no gain at q = 11 this round (the 240 sets look like strong local optima of this family); the transfer cards
gave three more cell improvements.

Late reports and Opus follow-up (01:30–02:10 UTC): c2 (LNS around 240, 2.8M steps, exact refills, branch and bound on
the union of the two 240 sets) found nothing above 240; every outside point is orthogonal to at least 8 set points.
**c6 q = 9: 150 flags** from an order-5 isometry of X4 = -8 X0 over GF(9) (146 from earlier seeds); Opus built and
checked **(11,7) 398,880** and **(12,7) 664,900** (uhcheck all sources + apsp_cyc VALID). Opus: isometries of order
11k (unipotent part; 45 classes sampled) give at most 221 at q = 11. The 240 isometry was recovered from its
permutation: g = 1 on the anisotropic plane A and a complex structure J (J^2 = -1) on the hyperbolic V4; the explicit
element (left multiplication by [[0,1],[-1,0]] on V4 = M2(F_q), det form) reproduces 240 in one 90 s run, but gives
only 88 at q = 7 (as card c5) and 206–218 at q = 13 (294 stays). Scripts: research/cell147/units/uni11/.

Opus, 02:00–02:30 UTC: the square-class points of E form the group (T × SL(2,q))/±1, and two of them conflict iff
their quotient (u, Y) has tr Y = u + 1/u. Right orbits of a subgroup K ≤ SL(2,q) without unipotents are then
independent. **The 240 set is two cosets of K = 2.A5** (order 120 = q^2 - 1 at q = 11; 132 orbits, at most 2
compatible), and 48 at q = 5 is two cosets of 2.A4 (order 24). At q = 7, 2.S4 (order 48) fits only one coset, and
subgroups of orders 6–24 give 72–80 (88 stays). Similitudes (sqrt(nu) on V4 times a similitude of A) at q = 13: at most 212.
So 2(q^2 - 1) is a Galois-exceptional (nearfield) phenomenon, not a general construction. Twisted cyclic groups R^a ⊕ Y^m at q = 7 (56 runs) gave at most 88; the one trivial
case (g = -1, all orbits single points, i.e. plain local search with orbitclique_q) hit **98 points at q = 7** (seed 1;
other seeds 82–96; 4 of 57 short runs reach 98). Opus built **(9,7) 117,844** (98 units; uhcheck all sources + apsp_cyc VALID). Plain local search at
q = 11 and 13 stays far below the orbit records (144, 201 after 5 min). The q = 7 98 set has stabilizer order 336: it is a union of PSL(2,7)
orbits (14 + 84) on V = Sym^4 ⊥ <n0> (binary quartics), whose 8 "centers" form the rational normal curve. The quartic
model at q = 11 gives at most 240 (PSL(2,11): 12 only; 2.A5: 60 + 6 × 30), and at q = 5 only 30. Longer q = 9 orbit
runs on card c6's order-5 isometries: 150 (no gain). GF(9) twisted cyclic groups R^a ⊕ Y^m (70 runs, uni11/q9/): at most 150. **(16,7) 4,023,516: full uhcheck over all 804,468 sources VALID** (03:18 UTC). (13,7) 1,063,416: apsp_cyc VALID (03:31 UTC).

## 2026-10-25 04:35–05:20 UTC, cell-14-7 third session, round 5 (8 cards, one squad): partial ovoids of Q(6,11) above 756

Session 01S9fS5Zi4bymqvTfraD7hJx (resumed job; master already had (14,7) 1,774,584 = 5·|H(11)| + 4·756 from the cell-13-7
session's 756-point partial ovoid). Goal: a pairwise-opposite point set of H(11) with 757+ points. Brief:
research/squads/d14D7-r5/BRIEF.md; new tools research/cell147/ovoid/ (orbclq.c: orbit graph + tabu max-weight clique,
finds the 756 set from scratch in 1–10 s; ovlib.py: all ten maximal tori of SO(7,q), invariant forms, conjugation to the
standard form; checkset.py). Cards: c1 principal PGL(2,11) on binary sextics · c2 J1 < G2(11) subgroups · c3 octonion
groups (G2(2), U3(3), 2^3·L3(2)) · c4 normaliser extensions of torus subgroups · c5 unipotent and Borel-type groups · c6
stabiliser of the 756 set, warm-started long runs · c7 wildcard: algebraic graphs in the affine chart · c8 wildcard:
Frobenius-twisted groups of the non-split tori.

Scores: c1 756 (S4, A4) · c2 756 (2^3:7:3 exact, Z6, Z7, 7:k) · c3 756 (octonion groups; late) · c4 368 · c5 232 · c6 756
(stabiliser in N(<h>) has order 120) · c7 181 · c8 756 (twisted C6 in N(C_1332)). Opus: torus sweeps (all cyclic subgroups
of orders 6–80 of the tori E·H·H, E·E·H, H4·H, E6 (1332), H6 (1330)): 756 again (orders 6–30), never more.

Opus: **the 756 set is one orbit of W(E7) = 2 × Sp(6,2)** acting on the E7 root lattice mod 11 (dreadnaut on the vector
graph: |Aut| = 2,903,040; W(E7) mod 11 has exactly 7 orbits on the 177,156 points, sizes 756, 10080, 12096, 15120, 30240,
48384, 60480, and only the 756 orbit is pairwise opposite; the q = 7 record 288 is likewise the W(E7) orbit mod 7). Every
group above that reached 756 is conjugate into Sp(6,2). Exact orbit cliques for all reflection subgroups of rank 6 of
W(E7): 756. Every point outside it is orthogonal to at least 60 of its points (60, 62, 70, 74, 76, 78 by orbit). So the
squad's verdict (756 is a plateau for symmetric searches) is explained, and plain partial ovoids look stuck.

What Opus did next (not a squad result): the surgery theorem needs less than pairwise opposite. R non-collinear, sigma(R)
non-concurrent and sigma a local duality at every point of R suffice (the (13,7) report's relaxed version); distance-4
pairs are then allowed when mirrored exactly on the line side. Adding points x to the 756 set (each at distance 4 from
60–78 of its points) with lines L_x chosen against the Hermitian spread gives a type-matching problem; greedy k = 9,
annealing k = 11. (14,7) 1,774,620 (k = 9) built by multi.c (local duality and non-concurrency checks, 11,734-source BFS
spot check: worst eccentricity 7); full check running. Squad assessment: no card beat 756; the round's value was
breadth (every family lands on the same W(E7) orbit), which pushed Opus off partial ovoids.

## 2026-10-25 05:38–06:40 UTC, cell-14-7 third session, round 6 (8 cards, one squad): mirrored extensions of R756

Goal: maximise F = (extra points) − (dropped base points) in the mirrored surgery (research/cell147/mirror/README.md;
|R'| = 756 + F, (14,7) n = 1,771,560 + 4|R'|). Opus had F = 11 (annealing). Scorer: mirror_build.py (re-checks
non-collinearity, opposition and exact mirroring of every distance-4 pair). Brief: research/squads/d14D7-r6/BRIEF.md.
Cards: c1 smarter annealing moves (C rewrite) · c2 ILP / iterated local search on fixed lines · c3 point sets with no
triple coverage, then line-only annealing · c4 point-side stars (12 points of a totally singular non-hexagon line) ·
c5 second Hermitian spreads S(n) · c6 genetic recombination · c7 wildcard: isometric copies of the base set · c8
wildcard: designed line families.

Scores: **c3 12** (verified, then built: (14,7) **1,774,632**, apsp_orb VALID) · c1 12 · c2 12 · c5 11 (any of 28
elliptic spreads gives the same plateau; mixing spreads costs 122 spread lines per foreign line) · c6 11 · c7 11 · c4 10
(stars make every base type a singleton, but the dual star's spread types are random 1/11, so the line side limits) ·
c8 (see scoreboard). K = 13 was reached by nobody with deficit 0 (c3: cost 1; Opus rerun: no gain).

Kept: c3's two-stage method. Opus then applied the same tools to the other hexagon cells: q = 5 F = 8 ((7,7) 23,596),
q = 7 F = 7 ((9,7) 118,238), both apsp_mt all-pairs VALID; q = 13 F = 21 ((16,7) 4,025,592, extra points at distance 4
from only 24–48 base points, spread of 2,198 lines; multi.c checks pass, full check running). Squad assessment: three
independent methods agree on F = 12 at q = 11; the round confirmed the plateau rather than moving it, but c3's method
gave the record and c4/c5 explained the limits.

Late reports (after 07:00 UTC): c2 (exact best responses on 20k-point and 20k-line samples, iterated local search from the
k = 11 state) reached F = 12 at k = 12 after 27 perturbations; at k = 13 it stalled at deficit 3. c7 (four random
isometric copies of the base set, 240 s each): F = 11 on one copy, 10 on the others and on the identity control, so
moving the base changes F by at most 1. c8 (12 extra points on a conic, a nondegenerate plane section of Q(6,11)):
F = -35; conic points give base types of size at most 2, but partner lines for the 66 pair types cannot be found
(deficit 47). Opus: fixed k = 13 with c1's C annealer warm-started from the k = 12 state, 436 s: best deficit 4 (c1's
own run: 5). So k = 13 with deficit 0 was not reached by any method (best deficits 1, 3, 4, 5); F = 12 stands.
Round 5 late report: c3's 2^3.L3(2) (1,344 signed Fano frames) subgroups all top out at 756, and exact branch and bound
is complete for orders 1344, 192, 168, 96, 56 and 48.

After the rounds (Opus, not a squad result): master meanwhile had (14,7) 1,788,052 from the cell-16-7 session's typed
levels, which leave the four non-friendly transitions without surgery. The 768-point mirrored sigma from this round fits
those transitions (its hypotheses are the one-transition surgery theorem's), giving (14,7) 1,789,588 (both hub sides
8,246 + 768) and a (15,7) candidate 2,499,748 (nine non-friendly transitions; spot check only). Plain all-pairs check
for (14,7): research/cell147/typedmirror/checks/. Exact one-pair extension test: no F = 12 state extends to F = 13.
