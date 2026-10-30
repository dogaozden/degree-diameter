r"""
Diameter 4, Theorem A: the Ahrens-Szekeres quadrangle AS(q), q odd, with one clone of every point of two
elliptic quadrics E_1, E_2 (a weighted 2-ovoid).  (q+2)-regular, 2 q^2 (q+2) vertices, diameter 4.
Sources: SYNTHETIC.md section 2.3 (Theorem A), research/gq4x/REPORT.md sections 1-2, research/gq4x/as_gq.py, as_w2.py.

Run:   sage d4_theoremA_ASq.sage           (checks q = 3 and q = 5)

Coordinates (research/gq4x/REPORT.md section 1).  F = GF(q), q odd.  The points of AS(q) are the q^3 elements
(a, (b, c)) of F x F^2 (the point (a, 1, b, c) of PG(3,q) off the plane x^perp of the symplectic quadrangle W(q)):
    (0, a, b, c)               a point of AS(q)
The lines (q+2 of them through every point, q points on each) are of two kinds:
    (1, 'A', p2, p3, a, b, c)  the coset line  { (a + l*D, b + l*p2, c + l*p3) : l in F },  D = b*p3 - c*p2,
                               in the direction (p2,p3) in {(0,1)} u {(1,t) : t in F}; the label uses the
                               unique point (a,b,c) of the line with c = 0 if (p2,p3) = (0,1), with b = 0 otherwise
                               (these are the isotropic lines of W(q) through a point of x^perp other than x)
    (1, 'B', b, c)             the fibre { (a, b, c) : a in F } over w = (b,c)  (the lines of W(q) through x
                               not in x^perp: the hyperbolic lines)
The clones:
    (0, 'clone', a, b, c, k)   the k-th clone (k = 1 or 2) of the point (0,a,b,c); it lies on every line through the point.
The two elliptic quadrics (weights): with eps a non-square of F and N(b,c) = b^2 - eps c^2,
    Q_k = { (c_k N(b,c), b, c) : b, c in F },  k = 1,2,   c_1 c_2 = 1/(4 eps);
every line of AS(q) meets Q_1 and Q_2 in exactly 2 points in total, and Q_1 and Q_2 share only (0,0,0), which gets weight 2.
"""
import itertools


def build_AS(q, F=None):
    r"""The quadrangle AS(q) (without clones).  Returns (G, points, lines, onl) where G is its incidence graph,
    onl[L] the list of points on line L (labels as above)."""
    F = F if F is not None else GF(q, 't')
    assert q % 2 == 1
    els = list(F)
    G = Graph(multiedges=False, loops=False)
    points = [(0, a, b, c) for a in els for b in els for c in els]
    G.add_vertices(points)
    directions = [(F(0), F(1))] + [(F(1), t) for t in els]
    lines, onl = [], {}
    # type A: the coset line through (a0, w0) in direction d.  Representatives: w0 on the transversal
    # c = 0 (d = (0,1)) or b = 0 (d = (1,t)); each coset has exactly one point there.
    for (p2, p3) in directions:
        for a in els:
            for s in els:
                b, c = (s, F(0)) if p2 == 0 else (F(0), s)
                D = b * p3 - c * p2
                L = (1, 'A', p2, p3, a, b, c)
                onl[L] = [(0, a + l * D, b + l * p2, c + l * p3) for l in els]
                lines.append(L)
    # type B: the fibres {(a, w) : a in F}
    for b in els:
        for c in els:
            L = (1, 'B', b, c)
            onl[L] = [(0, a, b, c) for a in els]
            lines.append(L)
    G.add_vertices(lines)
    # incidence of AS(q): every point is on the lines whose point set contains it
    for L in lines:
        for p in onl[L]:
            G.add_edge(p, L)
    return G, points, lines, onl


def weights_2ovoid(F, c1=None):
    """The weighted 2-ovoid w = 1_{Q_1} + 1_{Q_2}, as a dictionary point label -> weight (0, 1 or 2)."""
    els = list(F)
    squares = {x * x for x in els if x != 0}
    eps = next(x for x in els if x != 0 and x not in squares)          # a non-square
    c1 = F(c1) if c1 is not None else F(1)
    c2 = ~(F(4) * eps * c1)                                            # c1 * c2 = 1/(4 eps)
    N = lambda b, c: b * b - eps * c * c
    w = {}
    for ck in (c1, c2):
        for b in els:
            for c in els:
                p = (0, ck * N(b, c), b, c)
                w[p] = w.get(p, 0) + 1
    return w, eps, c1, c2


def build_d4_ASq(q, F=None, c1=None):
    r"""Theorem A graph: AS(q) plus one clone of each point of Q_1 and of Q_2 (two clones of (0,0,0))."""
    F = F if F is not None else GF(q, 't')
    G, points, lines, onl = build_AS(q, F)
    w, eps, c1, c2 = weights_2ovoid(F, c1)
    lines_on = {p: [] for p in points}
    for L in lines:
        for p in onl[L]:
            lines_on[p].append(L)
    # clones: (0,'clone',a,b,c,k) for k = 1..w(point); each clone is on every line through its point
    # (it has exactly the neighbours of the point it copies).
    for p, wt in sorted(w.items(), key=lambda kv: str(kv[0])):
        for k in range(1, wt + 1):
            cl = (0, 'clone') + p[1:] + (k,)
            for L in lines_on[p]:
                G.add_edge(cl, L)
    return G


# --------------------------------------------------------------------------------------------
# checks
# --------------------------------------------------------------------------------------------

def report(G, expect_n, expect_deg, expect_diam, bip=True, name=''):
    n = G.order()
    maxdeg = max(G.degree())
    isbip = G.is_bipartite()
    diam = G.diameter()
    ok = (n == expect_n and maxdeg == expect_deg and isbip == bip and diam == expect_diam)
    print(f'{name}: vertices {n} (expected {expect_n}), max degree {maxdeg} (expected {expect_deg}), '
          f'bipartite {isbip}, diameter {diam} (expected {expect_diam})  ->  {"OK" if ok else "MISMATCH"}')
    return ok


def check_quadrangle(q, F=None):
    """AS(q) is a generalized quadrangle of order (q-1, q+1): q points per line, q+2 lines per point, and
    for every anti-flag (p, L) exactly one point of L is collinear with p."""
    G, points, lines, onl = build_AS(q, F)
    assert all(len(onl[L]) == q for L in lines) and all(G.degree(p) == q + 2 for p in points)
    coll = {p: set() for p in points}
    for L in lines:
        for p in onl[L]:
            coll[p].update(onl[L])
    ok = True
    for L in lines:
        S = set(onl[L])
        for p in points:
            if p not in S and sum(1 for r in S if r in coll[p]) != 1:
                ok = False
    return ok


def check(q):
    """Theorem A at q: AS(q) is a GQ(q-1,q+1); the weights are a 2-ovoid; the clone graph has
    2 q^2 (q+2) vertices, is (q+2)-regular, bipartite, of diameter 4."""
    F = GF(q, 't')
    ok = True
    gq = check_quadrangle(q, F)
    print(f'AS({q}) is a generalized quadrangle of order ({q-1},{q+1}): {gq}')
    ok &= gq
    G0, points, lines, onl = build_AS(q, F)
    w, eps, c1, c2 = weights_2ovoid(F)
    sums = {sum(w.get(p, 0) for p in onl[L]) for L in lines}
    print(f'weighted 2-ovoid (eps={eps}, c1={c1}, c2={c2}): total weight {sum(w.values())}, line sums {sums}')
    ok &= (sums == {2})
    G = build_d4_ASq(q, F)
    ok &= report(G, 2 * q ** 2 * (q + 2), q + 2, 4, name=f'Theorem A, q={q}')
    print(f'   (q+2)-regular: {set(G.degree()) == {q + 2}}')
    ok &= (set(G.degree()) == {q + 2})
    return ok


if 'NO_AUTO_CHECK' not in globals():
    for q_ in (3, 5):
        assert check(q_)
