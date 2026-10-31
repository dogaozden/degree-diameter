# sd5b-r1 cards (goal (9,5) > 3,036: self-dual Haar graph of a group of order >= 1519, K = 9). Read COMMON.md first.

c1  SmallGroups of order 1561-1640 (skip 1568, 1584, 1600: too many groups) that have a normal Sylow p-subgroup of
    prime order p >= 19 on which G acts with order >= 3 (|G : C_G(P)| >= 3), center <= 6, at most 15 involutions.
    Filter in GAP first (see research/selfdual-d5/src/sg_filter.g), then export + sdtabu2 screen, smallest center first.
c2  Direct products G1 x G2, G1 a small non-abelian group (S3, D5, A4, Q8, Heis(3) = SmallGroup(27,3),
    SmallGroup(27,4), C7 : C3, C5 : C4, C13 : C3, ...) and G2 = C_p : C_q (q | p - 1, q >= 3) or another small group,
    order 1519-1650, that are NOT metacyclic. (The 2,970 graph was Heis(3) x (C11 : C5).)
c3  G = C_m : H with m odd composite (3p, 5p, 7p, pq) and H a NON-cyclic group of order k (C2 x C2k', Q8, Q16,
    C4 x C4, Dic, C3 x Q8, ...) acting on C_m through a cyclic quotient, order 1519-1650. Build with
    SemidirectProduct(H, hom, CyclicGroup(m)) (hom: H -> Aut(C_m)).
c4  Affine groups F_p^2 : H with H a NON-cyclic subgroup of GL(2,p) (dicyclic / quaternion, C_a x C_b diagonal,
    subgroups of GammaL(1,p^2), ...), p^2 |H| in 1519-1650 (p = 5, 7, 11, 13, 17, 19, 23, 29, 31, 37 ...). Use
    ConjugacyClassesSubgroups(GL(2,p)) filtered by order, build the affine group as a permutation group on F_p^2.
c5  Method card: simulated annealing inside the same family (copy research/selfdual-d5/src/sdtabu2.c to your folder,
    replace the tabu step by Metropolis acceptance of ONE random move with a temperature schedule and reheats),
    tested on the near misses SmallGroup(1539,31) record 1 type (1,4) and SmallGroup(1539,45) record 3 type (3,3)
    (sdtabu2 gets 2 there). Calibrate on C197 : C7 first (solutions per 100 s vs sdtabu2).
c6  Method card: compound moves. Copy sdtabu2.c; add moves that replace TWO items at once (sampled), or restart from
    perturbed elite states (keep the 10 best states seen, restart from one with 2 items changed) instead of random
    restarts. Same near misses and calibration as c5.
c7  Wildcard: non-solvable groups and groups without a large normal cyclic subgroup at order 1519-1700: SL(2,5) x C13,
    A5 x C26, A5 x D13, SL(2,5) x C14, A5 x C27, PSL(2,7) x C10, SL(2,7) x C5, (A5 x A5) is too big, A5 x (C3 x C9),
    GL(2,4) x ..., SmallGroups of these orders with a non-solvable composition factor. Export + sdtabu2 screen.
c8  Wildcard: find an approach none of the other cards uses (c1 SmallGroups 1561-1640 with normal C_p, c2 direct
    products, c3 C_m : H non-cyclic H, c4 affine F_p^2 : H, c5 annealing, c6 compound moves/elite restarts, c7
    non-solvable groups; the director runs metacyclic, F_p^d : C_k and SmallGroups 1520-1560 with normal C_p). Ideas:
    beta of order 4 (psi of order 4 orbits), groups of order 1519-1560 with 16-40 involutions, semidirect products
    (C_p x C_p) : C_k with reducible action, ... Say in the scoreboard line what you did.
