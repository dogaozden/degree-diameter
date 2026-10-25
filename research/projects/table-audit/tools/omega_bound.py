"""Counting bound for Gomez's Omega H(q) as read in tools/omega_build.py (table-audit).

Model: B_1 = H(q) incidence graph; hubs of label x are joined only to vertices labelled x (p_x or l_x = sigma(p_x),
sigma any bijection), 2 copies per group of 5; in type-a copies nbar-hubs sit on p_x and n-hubs on l_x, in type-b copies
the other way round.  Take a hub h = nbar_k(x) and a type-a copy C that h does not touch, and a point s of C.  h and s
have different colours, so D <= 8 needs d(h, s) <= 7.  A path leaves h (1 edge), walks inside copies (lengths a, b, ..)
and changes copy only through hubs (2 edges per hop, label kept; a hop between a type-b and a type-a copy swaps
p_y <-> l_y, a hop between two type-a copies keeps the vertex).  The number of points s such a path can reach is at most
  one hop  (3 + a + b <= 7):  type-a start: points within 4 of p_x;
                              type-b start at l_x: l_y at distance 0/2/4 from l_x, then points within 4/2/0 of p_y;
                                                   p_y at distance 1/3 from l_x, then points within 3/1 of l_y;
  >= 2 hops (1 + 2m + w <= 7, so w <= 2): at most 2 + 6(1 + q(q+1)) + 12(q+1)^2 (labels reachable by walks of total
                                          length <= 2 between label-preserving hops).
H(q) spheres: from a point, points at distance 2, 4, 6: q(q+1), q^3(q+1), q^5; lines at distance 1, 3, 5: (q+1),
q^2(q+1), q^4(q+1); the same from a line.  If the bound is below the number of points of C, some point of C is at
distance >= 9 from h, so the diameter is at least 9."""


def bound(q):
    P2, P4 = q * (q + 1), q ** 3 * (q + 1)          # points at distance 2, 4 from a point (also lines from a line)
    L1, L3 = q + 1, q * q * (q + 1)                  # lines at distance 1, 3 from a point (also points from a line)
    within4 = 1 + P2 + P4
    one_hop = within4 + P2 * (1 + P2) + P4 + L1 * L1 + L1 * (L1 + L3) + L3 * L1
    multi = 2 + 6 * (1 + P2) + 12 * L1 * L1
    return one_hop + multi


for q, cell in ((7, '(10,8)'), (8, '(11,8)'), (9, '(12,8)'), (11, '(14,8)'), (13, '(16,8)')):
    pts = (q ** 6 - 1) // (q - 1)
    b = bound(q)
    print(f'q = {q:2d} {cell}: reachable points <= {b:7d} < {pts:7d} points per copy: {b < pts}')
