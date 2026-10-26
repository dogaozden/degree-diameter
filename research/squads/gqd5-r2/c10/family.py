"""Explicit partial ovoid of W(q) (q odd prime power), size 3q-1 for q >= 5, in the coordinates of gqlib.W(q):
collinearity is w(x,y) = x0y2 + x1y3 - x2y0 - x3y1 = 0.

Construction (torus orbits). Let a_1=(1,0), a_2=(0,1), a_3=(1,1) in F_q^2 and v^perp = (-v1, v0) (so u.v^perp = 0
iff u = v up to scalar, for the dot product u.v = u0v0+u1v1). Put b_i = a_{i-1}^perp (indices mod 3) and, for c in F_q^*,
  O_i = { (a_i0, a_i1, c*b_i0, c*b_i1) : c in F_q^* }      (q-1 points each, i = 1,2,3)
Two extra points on the totally isotropic lines {x2=x3=0} and {x0=x1=0}:
  (x0, x1, 0, 0) with x = (1,t), t not in {0,1};   (0,0,y0,y1) with y = z^perp, z not in {a_1,a_2,a_3,x}, x.y != 0.
Claim: the union is a partial ovoid of size 3(q-1)+2 = 3q-1.

Proof sketch (w = dot-form computation). For P = (a, c b) and P' = (a', c' b') the form is
  w(P,P') = c'(a.b') - c(b.a').
(i) inside O_i: w = (c'-c)(a_i.b_i), and a_i.b_i = a_i.a_{i-1}^perp != 0 since a_i != a_{i-1}.
(ii) O_i vs O_j (i != j): w = 0 needs c'(a_i.b_j) = c(b_i.a_j) with c,c' nonzero; a_i.b_j = 0 iff a_i = a_{j-1}, and
     b_i.a_j = 0 iff a_j = a_{i-1}. For the 3 distinct a's exactly one of these holds for every pair, so one factor is 0
     and the other nonzero, so no solution with c,c' in F_q^*.
(iii) (x,0,0) vs O_i: w = c(x.b_i) = 0 iff b_i = x^perp iff a_{i-1} = x, excluded since x != a_k.
(iv) (0,0,y) vs O_i: w = -(y.a_i) = 0 iff a_i = y^perp = z, excluded.
(v) (x,0) vs (0,y): w = x.y != 0.  Two points on one isotropic line are never a problem since each extra line contributes one point.
The code below checks all of this numerically with gqlib.is_partial_ovoid.
"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'theorems', 'd5gq'))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'theorems', 'chartlift'))
from gf import GF
import gqlib


def norm(F, v):
    for x in v:
        if x:
            s = F.inv[x]
            return tuple(F.mul[s][y] for y in v)
    raise ValueError


def family_points(q):
    """Return list of projective point tuples (normalized) of the partial ovoid of W(q), q odd >= 5."""
    F = GF(q)
    neg = F.neg
    perp = lambda v: (neg[v[1]], v[0])
    dot = lambda u, v: F.add[F.mul[u[0]][v[0]]][F.mul[u[1]][v[1]]]
    a = [(1, 0), (0, 1), (1, 1)]
    b = [perp(a[(i - 1) % 3]) for i in range(3)]          # b_i = a_{i-1}^perp
    pts = []
    for i in range(3):
        for c in range(1, q):
            v = (a[i][0], a[i][1], F.mul[c][b[i][0]], F.mul[c][b[i][1]])
            pts.append(norm(F, v))
    # extra points: x = (1,t) with t not in {0,1}; z not in {a_1,a_2,a_3,x}; y = z^perp with x.y != 0
    PG1 = [(1, t) for t in range(q)] + [(0, 1)]
    found = None
    for t in range(q):
        if t in (0, 1):
            continue
        x = (1, t)
        for z in PG1:
            if norm(F, z) in [norm(F, u) for u in a + [x]]:
                continue
            y = perp(z)
            if dot(x, y) != 0:
                found = (x, y); break
        if found:
            break
    if found is None:            # q = 3: only the 3(q-1) orbit points
        return pts
    x, y = found
    pts.append(norm(F, (x[0], x[1], 0, 0)))
    pts.append(norm(F, (0, 0, y[0], y[1])))
    return pts


def check(q):
    G = gqlib.W(q)
    pts = family_points(q)
    idx = [G.index[p] for p in pts]
    assert len(set(idx)) == len(idx)
    return len(idx), gqlib.is_partial_ovoid(G, idx)


if __name__ == '__main__':
    for q in [int(s) for s in sys.argv[1:]] or [5, 7, 9, 11, 13]:
        n, ok = check(q)
        print('W(%d): size %d (3q-1 = %d), partial ovoid: %s, 2q+1 = %d' % (q, n, 3 * q - 1, ok, 2 * q + 1), flush=True)
