"""W(3,q) in the K^2 model, with its regular spread.

K = GF(q^2), F = GF(q) inside K. Points of PG(3,q) = nonzero vectors (a,b) in K^2 modulo F*.
Symplectic form B(x,y) = Tr_{K/F}(a e - b c) for x = (a,b), y = (c,e). It is F-bilinear, alternating, nondegenerate.
Totally isotropic (t.i.) lines = lines of W(3,q).
Regular spread S = the K-points: the line {(k a, k b) : k in K*} for each (a:b) in PG(1,q^2). These are t.i.

Dually (Klein), W(3,q) points = lines of Q(4,q), W(3,q) lines = points of Q(4,q), the spread S = an elliptic quadric
ovoid O of Q(4,q). So "line copies of Q(4,q) with stand-ins, one ovoid copy" (NOTE.md, open problem 3) becomes:
a set M of points of W(3,q) with at most 1 point on every t.i. line outside S and at most 2 on every line of S.

Group: g in GL(2,K) with det g in F* preserves B up to the factor det g, and maps S to S.
Also x -> x^p coordinatewise (Frobenius) preserves B up to p-th power, so maps t.i. lines to t.i. lines, and S to S.
"""
import itertools
import sys
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parents[3] / 'problems' / 'bipartite_dd'))
import lib  # noqa: E402


class W3:
    def __init__(self, q):
        self.q = q
        Q = q * q
        K = lib.GF(Q)
        self.K = K
        self.add = K.add_table
        self.mul = K.mul_table
        self.neg = K._neg
        exp, log = K._exp, K._log
        self.exp, self.log = exp, log
        # F = elements with x^q = x: 0 and gamma^{(q+1)k}.
        self.F = [0] + [int(exp[(q + 1) * k]) for k in range(q - 1)]
        self.frob_q = np.array([0] + [int(exp[(int(log[x]) * q) % (Q - 1)]) for x in range(1, Q)])
        self.tr = np.array([self.add[x, self.frob_q[x]] for x in range(Q)])  # Tr_{K/F}
        # Points: normalise first nonzero coord to have log < q+1 (coset reps of F* in K*).
        pts = []
        idx = {}
        for a in range(Q):
            for b in range(Q):
                if a == 0 and b == 0:
                    continue
                v = self.norm((a, b))
                if v not in idx:
                    idx[v] = len(pts)
                    pts.append(v)
        self.pts, self.idx = pts, idx
        n = len(pts)
        assert n == (q ** 4 - 1) // (q - 1)
        # Spread lines: K-points.
        sp_of = [-1] * n
        spread = []
        for i, (a, b) in enumerate(pts):
            if sp_of[i] >= 0:
                continue
            L = sorted({idx[self.norm((self.mul[k, a], self.mul[k, b]))] for k in range(1, Q)})
            assert len(L) == q + 1
            for p in L:
                sp_of[p] = len(spread)
            spread.append(tuple(L))
        self.spread, self.sp_of = spread, sp_of
        # t.i. lines.
        A = np.array([p[0] for p in pts])
        Bv = np.array([p[1] for p in pts])
        lines = set()
        on = [[] for _ in range(n)]
        Fnz = self.F[1:]
        for i in range(n):
            a, b = pts[i]
            # B(x,y) = Tr(a e - b c), y = (c,e)
            val = self.tr[self.add[self.mul[a, Bv], self.neg[self.mul[b, A]]]]
            for j in np.nonzero(val == 0)[0]:
                j = int(j)
                if j <= i:
                    continue
                c, e = pts[j]
                L = {i, j}
                for lam in Fnz:
                    L.add(idx[self.norm((self.add[a, self.mul[lam, c]], self.add[b, self.mul[lam, e]]))])
                lines.add(tuple(sorted(L)))
        lines = sorted(lines)
        assert len(lines) == n, (len(lines), n)
        self.lines = lines
        for j, L in enumerate(lines):
            assert len(L) == q + 1
            for p in L:
                on[p].append(j)
        assert all(len(o) == q + 1 for o in on)
        self.on = on
        spset = set(spread)
        self.is_spread_line = [L in spset for L in lines]
        assert sum(self.is_spread_line) == q * q + 1

    def norm(self, v):
        a, b = v
        lead = a if a else b
        lg = int(self.log[lead])
        r = lg % (self.q + 1)
        if lg == r:
            return (int(a), int(b))
        s = int(self.exp[(r - lg) % (self.q * self.q - 1)])
        return (int(self.mul[s, a]), int(self.mul[s, b]))

    # --- group elements as point permutations ---
    def mat_perm(self, g):
        """g = (g11,g12,g21,g22) in K, det in F*. Acts on column vectors (a,b)."""
        g11, g12, g21, g22 = g
        perm = []
        for a, b in self.pts:
            na = self.add[self.mul[g11, a], self.mul[g12, b]]
            nb = self.add[self.mul[g21, a], self.mul[g22, b]]
            perm.append(self.idx[self.norm((na, nb))])
        return perm

    def frob_perm(self, e=1):
        p = self.K.p
        perm = []
        for a, b in self.pts:
            perm.append(self.idx[self.norm((self.K.pow(a, p ** e) if a else 0, self.K.pow(b, p ** e) if b else 0))])
        return perm

    def det(self, g):
        g11, g12, g21, g22 = g
        return int(self.add[self.mul[g11, g22], self.neg[self.mul[g12, g21]]])

    def in_F(self, x):
        return x in set(self.F)


def orbits(n, gens):
    """Orbits of the group generated by the permutations gens on range(n)."""
    seen = [-1] * n
    orbs = []
    for s in range(n):
        if seen[s] >= 0:
            continue
        orb = [s]
        seen[s] = len(orbs)
        k = 0
        while k < len(orb):
            x = orb[k]
            k += 1
            for g in gens:
                y = g[x]
                if seen[y] < 0:
                    seen[y] = len(orbs)
                    orb.append(y)
        orbs.append(orb)
    return orbs, seen


if __name__ == '__main__':
    for q in map(int, sys.argv[1:]):
        W = W3(q)
        print(q, len(W.pts), len(W.lines), len(W.spread))
