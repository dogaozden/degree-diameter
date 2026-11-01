# deep-65 working notes (Opus, Nov 1 2026)

## Lead (b): Haar + hub orbits, type 1,6|1,6

### Clean model
The t18 parameters (S, g1, g2, H, K) only matter through KA = g1 K g1^-1 and HB = g2^-1 H g2. Model:
G of order m, S subset of G with |S| = 5, KA and HB subgroups of order 6.
- A0 = G, B0 = G, x ~ xs (s in S)
- B1 = G/KA: the hub of the left coset xKA is adjacent to the 6 vertices of xKA (in A0)
- A1 = G/HB: the hub of the left coset yHB is adjacent to the 6 vertices of yHB (in B0)
6-regular, bipartite, n = 2m + 2m/6 = 7m/3 (m = 294 gives 686). G acts by left multiplication.

### Diameter 5 as six covering conditions
In a bipartite graph, diameter <= 5 iff every same-side pair is at distance <= 4 (for a in A, b in B take a neighbour
a' of b: d(a,b) <= d(a,a') + 1). Writing T = S S^-1, T' = S^-1 S and reading off the walks of length <= 4:
1. A0-A0: {e} u T u KA u TT u T KA u KA T u S HB S^-1 = G
2. A0-A1: (T u KA) S HB = G
3. A1-A1: HB T' HB = G
4. B0-B0: {e} u T' u HB u T'T' u T' HB u HB T' u S^-1 KA S = G
5. B0-B1: (T' u HB) S^-1 KA = G
6. B1-B1: KA T KA = G
Checked: tools/hubeval.c on the c18 cost-2 state (SmallGroup(294,11)) gives (1) missing exactly 2 elements (74, 214 =
inverse pair), all others 0; its rebuilt edge list scores bad = 294 with score65, identical to c18/cost2_294_11.edges.

### Symmetry reduction (why 1e12 was 5e8)
(S, KA, HB) ~ (d^-1 S c, d^-1 KA d, c^-1 HB c) for all d, c in G (relabel A0 by x -> xd, B0 by y -> yc), and
~ (S^-1, HB, KA) (swap sides). So KA and HB can be fixed to conjugacy-class representatives; then only
d in N(KA), c in N(HB) remain, and every S is equivalent to one containing the representative of its smallest
N(KA) x N(HB)-orbit. c28's count (49^4 x C(294,5) / |Aut|) treated g1, g2 as free on top of H, K, but they only conjugate.
On SmallGroup(294,11) all 49 subgroups of order 6 are cyclic and conjugate (Hall subgroups), N(C6) = C6, so the search
is one class pair, 6.5e8 subsets.

### Exact result on SmallGroup(294,11)
tools/hubex.c, 76 s on one core: 649,970,936 subsets enumerated, 164,080,912 pass (6)(3), 67,346 pass (2)(5),
**0 solutions**, best = 2 missing elements (12 subsets, the known cost-2 states). The family 1,6|1,6 on 294_11 is closed:
cost 2 is the global minimum, not a local one.

Validation of the reduction: NORED=1 (all subgroup pairs, all subsets, no symmetry) and the reduced search agree on
existence and best value for all 157 groups of orders 24-56 with d = 4 (10 with solutions, 147 without). Solutions
found there rebuild (hubeval) to graphs that apsp.c calls VALID at D = 5 and INVALID at D = 4 (n = 70, d = 4).

### All 23 groups of order 294 (n = 686): closed
tools/hubex.c on every SmallGroup(294, i) (one class of order-6 subgroups in each; S3 hubs where those are the order-6
subgroups). No solution in any group. Best missing count (1)+(4) among subsets passing (2),(3),(5),(6):
294_11 2, **294_12 3** (t18 tabu had 4), 294_7 7 ((C7 x C7):S3, S3 hubs; c26 also found 7), 294_17 16, 294_1 17,
294_9 18, 294_8 19, 294_14 21, 294_13 28, 294_10 66; the other 12 groups have no S passing (2),(3),(5),(6) at all.
Runs: 6 to 86 s per group. So the 1,6|1,6 family has no graph of diameter 5 on 686 vertices.

## The cost-2 graph as a lift
nauty: Aut(cost-2 graph) has order exactly 294 (4 orbits), so it is not part of a more symmetric object.
The normal C7 x C7 of SmallGroup(294,11) meets the hub subgroups trivially, so it acts freely on all four orbits: the
graph is a regular lift of a 14-vertex base (6 + 1 per side: a_i ~ b_(i+u) three times, b_(i+v), b_(i+w), hub; the
hub alpha ~ all b_j) by C7 x C7 (tools/hub2lift.py writes it in the vl format of shared/tabu.c; lift cost 12 = 6 A0
sources x 2). In that bigger family (29 free voltages): shared/kopt K = 2 from the cost-2 state, 900,792 candidates,
no cost-0 lift; tabu from random voltages reaches only 76 in 90 s and tabu from the cost-2 state stays at 12.
So breaking the C6 symmetry does not open a way down; the symmetric family is the better search space.
