"""PG(2,q) with a conic and its polarity, and the hat structures of SYNTHETIC.md Section 1.

Points and lines are normalized triples over GF(q) (GF from research/plus2/coords/coords.py);
a point p is on a line L iff p . L = 0.  For odd q the conic is C: x z = y^2, with polarity
p = (x,y,z) -> p^perp = [z, -2y, x] (and [a,b,c] -> (c, -b/2, a)).  After the plane is built, the hat structures use only
incidence (they follow the six rules (R1)-(R6) of SYNTHETIC.md, Definition 1.1).
"""
import itertools
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[1] / 'plus2' / 'coords'))
import coords  # noqa: E402


class PG2:
    def __init__(self, q):
        self.q = q
        F = self.F = coords.GF(q)
        els = range(q)
        self.points = sorted({('p', coords.normalize(F, v)) for v in itertools.product(els, repeat=3) if any(v)})
        self.lines = sorted({('L', coords.normalize(F, v)) for v in itertools.product(els, repeat=3) if any(v)})
        self.pts_on = {L: set() for L in self.lines}
        self.lines_on = {p: set() for p in self.points}
        for p in self.points:
            for L in self.lines:
                if coords.dot(F, p[1], L[1]) == 0:
                    self.pts_on[L].add(p)
                    self.lines_on[p].add(L)
        self.inc = {(p, L) for L in self.lines for p in self.pts_on[L]}

    def pt(self, v):
        return ('p', coords.normalize(self.F, v))

    def ln(self, v):
        return ('L', coords.normalize(self.F, v))

    def join(self, p, r):
        (L,) = self.lines_on[p] & self.lines_on[r]
        return L

    def meet(self, L, N):
        (p,) = self.pts_on[L] & self.pts_on[N]
        return p

    # --- the conic x z = y^2 and its polarity (q odd)
    def perp(self, x):
        F = self.F
        a, b, c = x[1]
        if x[0] == 'p':                       # point -> line B p,  B = [[0,0,1],[0,-2,0],[1,0,0]]
            return ('L', coords.normalize(F, (c, F.neg(F.add(b, b)), a)))
        h = F.inv(F.add(1, 1))                # line -> point B^-1 L
        return ('p', coords.normalize(F, (c, F.neg(F.mul(h, b)), a)))

    def conic(self):
        F = self.F
        return {p for p in self.points if F.mul(p[1][0], p[1][2]) == F.mul(p[1][1], p[1][1])}


def hats(Pi, A, ell, X, kind):
    """The three-hat (kind 'AL', labels 0,1,'a') or four-hat (kind '4', labels 0,1,'a','c')
    structure of SYNTHETIC.md Definition 1.1.  Returns the set of flags.
    New points ('Q',), ('H',s); new lines ('M',), ('K',s)."""
    S = list(X)
    lam = {s: Pi.join(A, X[s]) for s in S}
    if kind == 'AL':
        T, link, removed, rot = [0, 1], {0: 1, 1: 0}, ['a'], {}
    else:
        T = [0, 1, 'c']
        link = {0: 'c', 'c': 1, 1: 0}
        removed, rot = S, link
    inc = set(Pi.inc)
    for s in removed:
        inc.remove((X[s], lam[s]))
    for t, u in rot.items():
        inc.add((X[t], lam[u]))
    for s in S:
        for N in Pi.lines_on[X[s]] - {ell}:
            inc.add((('H', s), N))
        for p in Pi.pts_on[lam[s]] - {A}:
            inc.add((p, ('K', s)))
        inc.add((('H', s), ('M',)))
        inc.add((('Q',), ('K', s)))
    for p in Pi.pts_on[ell] - {X[t] for t in T}:
        inc.add((p, ('M',)))
    for N in Pi.lines_on[A] - {lam[t] for t in T}:
        inc.add((('Q',), N))
    inc.add((A, ('K', 'a')))
    inc.add((('H', 'a'), ell))
    for t in T:
        inc.add((('H', t), ('K', link[t])))
    return inc


def split(inc):
    pts = sorted({p for p, _ in inc}, key=repr)
    lns = sorted({L for _, L in inc}, key=repr)
    lines_on = {p: set() for p in pts}
    pts_on = {L: set() for L in lns}
    for p, L in inc:
        lines_on[p].add(L)
        pts_on[L].add(p)
    return pts, lns, lines_on, pts_on


def diameter3(inc):
    """True iff any two points are collinear and any two lines concurrent (Lemma 0.1(a))."""
    pts, lns, lines_on, pts_on = split(inc)
    for u, v in itertools.combinations(pts, 2):
        if not lines_on[u] & lines_on[v]:
            return False
    for u, v in itertools.combinations(lns, 2):
        if not pts_on[u] & pts_on[v]:
            return False
    return True
