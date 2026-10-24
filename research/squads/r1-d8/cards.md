# r1-d8 cards (one strategy each; scorer: research/theorems/d8/liftdiam; README.md has the tools)

Common goal: a STRUCTURED lift of H(q) + 2 hop matchings (degree q+3) with diameter 8 and as many copies M as possible.
Test bed q = 5 (|GH(5)| = 7812): random reaches M ~ 12; DGQ's formula gives 25; M >= 27 would be a new (8,8) record
(27*7812 = 210,924 > 206,448). If something reaches >= 20 at q=5, try q = 7 (target M >= 31 beats (10,8) = 1,176,480).

c1  Pencil labels. Fix two linear forms f,g on GF(q)^7; for a point p (vector v) let c(p) = [f(v):g(v)] in PG(1,q),
    numbered cyclically through GF(q^2)*/GF(q)* (so Z_{q+1}) or by discrete log; points with f=g=0 get a special
    label. Use c(p) (or a function of it) as the Z_k label of hop k at p, in Z_5 x Z_k with Z_5 voltages (1,2) on the
    hops (polygon cover); choose s_k by a geometric rule (e.g. s_k(p) = a line through p chosen by f/g, or random).
c2  Quadratic holonomy. Put Z_k voltages on the H(q) flags from a quadratic/square-class rule (e.g. for flag (p,L)
    use the square class or the value class {t,-t} of a coordinate ratio along L), Z_5 x Z_k with polygon-cover Z_5
    on hops. Goal: the q+1 geodesics between opposite elements should get many different voltages.
c3  Annealing. Simulated annealing over the Z_k labels of the hops (and optionally of the H(q) flags) with the Z_5
    part fixed to the polygon cover, cost = liftdiam unreached (SRC_STEP 4-8 for speed, confirm with step 1).
    Start at q=5, k=4, then k=5,6. Report best M with unreached 0.
c4  Torus symmetry. Make everything invariant under the diagonal torus T of G_2(q) (README): s_k T-equivariant
    (choose s_k on orbit representatives), labels constant on T-orbits. Search orbit labels (random restarts + hill
    climbing on liftdiam unreached). Any group: Z_M or Z_5 x Z_k.
c5  Colour voltages, cyclic group. Properly colour the flags of H(q) with q+1 colours (perfect matchings of the
    incidence graph; e.g. repeated random perfect matchings, or a geometric rule), give colour c the voltage v_c in
    Z_M, hops get voltages w_1, w_2; search over (v_c, w_k, M) for the largest M with unreached 0.
c6  One extra edge (j = 1, degree q+2). Any structured idea. Targets: q = 5 M >= 11 beats (7,8) = 82,992 (11*7812 =
    85,932); q = 7 M >= 12 beats (9,8) = 453,840. Note the n+2 cover with one hop of voltage 1 in Z_4 is the trivial
    baseline (M = 4).
c7  Wildcard: find an approach none of c1-c6, c8 uses (pencil labels, quadratic holonomy, annealing, torus symmetry,
    colour voltages, j=1, permutation/two-hexagon lifts). Implement and score it.
c8  Wildcard 2: non-group levels or a second hexagon. E.g. hops s(p) = gamma(line through gamma^{-1}(p)) for a
    collineation gamma of the quadric that does not preserve H(q) (any orthogonal map), or levels permuted by
    non-commuting permutations (write a small BFS checker for permutation voltages if needed). Score it.
