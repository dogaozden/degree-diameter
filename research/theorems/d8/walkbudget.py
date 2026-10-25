"""Expected number of reduced walks of length <= 7 from a point x to a line y in H(q) + j random hop matchings
(exact first-order formula: hop endpoints treated as uniform), split by number of hops; compared with DGQ's M."""
from fractions import Fraction as Fr
def counts(q):
    P = (q**6 - 1)//(q - 1)
    # elements at distance a from a point (points for even a, lines for odd a) and geodesic multiplicity
    m = {0: 1, 1: q+1, 2: q*(q+1), 3: q*q*(q+1), 4: q**3*(q+1), 5: q**4*(q+1), 6: q**5}
    g = {a: (q+1 if a == 6 else 1) for a in range(7)}
    return P, m, g
def budget(q, j):
    P, m, g = counts(q)
    # one hop: x ~a~ u -hop- u' ~b~ y, a+b+1 <= 7 odd: a+b even <= 6. distances from a line are the same numbers.
    E1 = sum(Fr(m[a]*g[a]*m[b]*g[b], P) for a in range(7) for b in range(7) if (a+b) % 2 == 0 and a+b <= 6)
    # two hops: a+b+c+2 <= 7 and odd total: a+b+c odd <= 5; middle segment any parity consistent (b counted as walk from hop end)
    E2 = sum(Fr(m[a]*g[a]*m[b]*g[b]*m[c]*g[c], P*P) for a in range(6) for b in range(6) for c in range(6) if (a+b+c) % 2 == 1 and a+b+c <= 5)
    # three hops: a+b+c+d+3 <= 7, a+b+c+d even <= 4
    E3 = sum(Fr(m[a]*m[b]*m[c]*m[d], P**3) for a in range(5) for b in range(5) for c in range(5) for d in range(5) if (a+b+c+d) % 2 == 0 and a+b+c+d <= 4)
    return 1, j*E1, j*j*E2*P, j**3*E3*P*P  # E2, E3 normalised: each segment endpoint lands uniformly
for q, j, M in [(7,2,30),(8,2,30),(9,2,35),(11,2,40),(13,2,45),(11,1,15),(4,2,20),(5,2,25),(3,2,20)]:
    b = budget(q, j)
    W = sum(float(x) for x in b)
    print(f"q={q:2d} j={j} DGQ M={M:3d}  walks: geodesic 1, one-hop {float(b[1]):7.1f}, two-hop {float(b[2]):6.1f}, three-hop {float(b[3]):5.1f}  total W={W:7.1f}  W/M={W/M:4.2f}")
