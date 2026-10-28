"""Explicit duality phi of W(q), q even, via the Klein correspondence and the nucleus projection.

Lines of W(q) -> Plucker coordinates p_ij = x_i y_j - x_j y_i; t.i. for w = x0y2+x1y3+x2y0+x3y1 means p02 = p13 (char 2).
Then (p01, p23, p03, p12) is a point of PG(3,q) lying on the parabolic quadric u0u1+u2u3 = p02^2 (Klein quadric section),
so Lam: lines(W) -> points(PG(3,q)) is a bijection; the t.i. lines of the form B'(u,v)=u0v1+u1v0+u2v3+u3v2 are the
images of the stars of W-points.  tau(u)=(u0,u2,u1,u3) carries B' to w.  Then
  phi_line(L) = tau(Lam(L))          (line -> point)
  phi_pt(p)   = the W-line whose points are {phi_line(L): L through p}   (point -> line)
and incidence p I L <=> phi_line(L) I phi_pt(p) is checked numerically.
"""
import sys, os, json
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d5gq')
import gqlib

OUT = os.path.dirname(os.path.abspath(__file__))


def duality(q):
    G = gqlib.W(q)
    F = G.F; pts = G.coords; index = G.index
    sub, mul, add = F.sub, F.mul, F.add
    def pl(x, y, i, j):
        return sub[mul[x[i]][y[j]]][mul[x[j]][y[i]]]
    lam = []
    for L in G.lines:
        x, y = pts[L[0]], pts[L[1]]
        p01, p02, p03 = pl(x, y, 0, 1), pl(x, y, 0, 2), pl(x, y, 0, 3)
        p12, p13, p23 = pl(x, y, 1, 2), pl(x, y, 1, 3), pl(x, y, 2, 3)
        assert p02 == p13, 'line not totally isotropic'
        u = (p01, p23, p03, p12)
        assert add[mul[p01][p23]][mul[p03][p12]] == mul[p02][p02], 'Klein relation fails'
        lam.append(index[gqlib._norm(F, u)])
    assert len(set(lam)) == G.nl, 'Lam not injective'
    phi_line = [index[gqlib._norm(F, (pts[i][0], pts[i][2], pts[i][1], pts[i][3]))] for i in lam]
    assert len(set(phi_line)) == G.np, 'phi_line not injective'
    linedict = {frozenset(l): i for i, l in enumerate(G.lines)}
    phi_pt = []
    for p in range(G.np):
        S = frozenset(phi_line[L] for L in G.plines[p])
        assert S in linedict, 'star image is not a line'
        phi_pt.append(linedict[S])
    assert sorted(phi_pt) == list(range(G.nl))
    I = G.I
    J = I[np.ix_(np.array(phi_line), np.array(phi_pt))]   # J[L,p] = I[phi_line(L), phi_pt(p)]
    assert np.array_equal(J, I.T), 'incidence not preserved'
    return G, phi_pt, phi_line


if __name__ == '__main__':
    for q in (2, 4, 8):
        G, pp, pl_ = duality(q)
        with open(os.path.join(OUT, 'phi_q%d.json' % q), 'w') as f:
            json.dump({'q': q, 'graph': G.name, 'np': G.np, 'nl': G.nl,
                       'point_to_line': pp, 'line_to_point': pl_,
                       'check': 'p I L <=> line_to_point[L] I point_to_line[p], verified'}, f)
        print('q=%d verified duality, points %d lines %d' % (q, G.np, G.nl), flush=True)
