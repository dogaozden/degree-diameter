"""Orbit structure of S for the records that orbit_check.py does not handle: G = Q x Z_n with Q a product of two
matrix groups, or a matrix group over GF(p^e) with e > 1.

Usage: python3 orbit_check2.py SOL.txt k [swap]

Searches alpha(x_1, x_2, z) = (g_1 x_1 g_1^-1, g_2 x_2 g_2^-1, r z) (one factor: (g x g^-1, r z)) with r of order
dividing k mod n, and c in S, such that S is closed under beta(x) = alpha(x) * c, and prints the cycle sizes of beta on
S (see orbit_check.py for why c appears).  With the extra argument `swap` (two equal factors) it searches instead
alpha(x_1, x_2, z) = (g x_2 g^-1, x_1, r z), the order-6 symmetry of the (13,8) record, with c = e.

The group arithmetic is taken from research/frontier/build_haar2.py (its Field and Matrix classes). This is a check of
the search structure only; it plays no role in the diameter checks.
"""
import importlib.util
import os
import re
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("bh2", os.path.join(HERE, "../../frontier/build_haar2.py"))
bh2 = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bh2)


class Fac:
    """one matrix factor: all elements as entry arrays, and helpers on canonical keys"""

    def __init__(self, M):
        self.M = M
        F = M.F
        self.A, self.Mu, self.neg, self.inv = F.add, F.mul, F.neg, F.inv
        a, b, c, d = M.entries(np.arange(M.order))
        self.all = (a, b, c, d)

    def mul(self, x, y):
        A, Mu = self.A, self.Mu
        a, b, c, d = x
        e, f, g, h = y
        return (A[Mu[a, e], Mu[b, g]], A[Mu[a, f], Mu[b, h]], A[Mu[c, e], Mu[d, g]], A[Mu[c, f], Mu[d, h]])

    def inverse(self, x):          # determinant 1 (SL, PSL): [[d, -b], [-c, a]]
        a, b, c, d = x
        assert self.M.kind in ("sl", "psl")
        return (d, self.neg[b], self.neg[c], a)

    def key(self, x):
        a, b, c, d = (np.asarray(t) for t in x)
        return int(self.M.canon_key(np.atleast_1d(a), np.atleast_1d(b), np.atleast_1d(c), np.atleast_1d(d))[0])

    def conj_solutions(self, x, y):
        """all g with g x g^-1 = y (as group elements, i.e. up to sign in PSL)"""
        G = self.all
        lm = self.mul(G, x)
        sols = []
        signs = [y]
        if self.M.kind == "psl" and self.M.q % 2:
            signs.append(tuple(self.neg[t] for t in y))
        for yy in signs:
            rm = self.mul(yy, G)
            ok = (lm[0] == rm[0]) & (lm[1] == rm[1]) & (lm[2] == rm[2]) & (lm[3] == rm[3])
            sols += [tuple(int(t[i]) for t in G) for i in np.flatnonzero(ok)]
        return sols


def parse_mat(s):
    return tuple(int(t) for t in s.split(","))


def main():
    path, k = sys.argv[1], int(sys.argv[2])
    swap = len(sys.argv) > 3 and sys.argv[3] == "swap"
    lines = [ln for ln in open(path).read().split("\n") if ln.strip()]
    head = lines[0].split()
    d = int(head[0])
    ni = head.index("n")
    Q, j = bh2.parse_group(head[2:ni], 0)
    n = int(head[ni + 1])
    facs = [Fac(Q.g1), Fac(Q.g2)] if isinstance(Q, bh2.Prod) else [Fac(Q)]
    S = []
    for ln in lines[1:1 + d]:
        mats = re.findall(r"mat\(([^)]*)\)", ln)
        z = int(re.search(r"z=(\d+)", ln).group(1))
        S.append((tuple(parse_mat(m) for m in mats), z))
    nf = len(facs)

    def skey(s):
        return (tuple(facs[i].key(s[0][i]) for i in range(nf)), s[1] % n)
    Sset = {skey(s) for s in S}
    assert len(Sset) == d
    rs = [r for r in range(1, n) if np.gcd(r, n) == 1 and pow(r, k, n) == 1 % n] if n > 1 else [0]
    ident = tuple(facs[i].key((1, 0, 0, 1)) for i in range(nf))

    def cycles(beta):
        pos = {skey(s): t for t, s in enumerate(S)}
        seen, cyc = set(), []
        for t, s in enumerate(S):
            if t in seen:
                continue
            L, cur = 0, s
            while pos[skey(cur)] not in seen:
                seen.add(pos[skey(cur)])
                L += 1
                cur = beta(cur)
            cyc.append(L)
        return sorted(cyc)

    name = os.path.basename(path)
    if swap:
        assert nf == 2 and facs[0].M.spec == facs[1].M.spec
        F0 = facs[0]
        G = F0.all
        for idx in range(F0.M.order):
            g = tuple(int(t[idx]) for t in G)
            gi = F0.inverse(g)
            for r in rs:
                def beta(s):
                    (x1, x2), z = s
                    return ((F0.mul(F0.mul(g, x2), gi), x1), (r * z) % n)
                if all(skey(beta(s)) in Sset for s in S):
                    cyc = cycles(beta)
                    if max(cyc) > 1:
                        print(f"{name}: S closed under alpha(x1, x2, z) = (g x2 g^-1, x1, {r} z mod {n}) with g = mat{g}; "
                              f"cycle sizes of alpha on S: {cyc}")
                        return 0
        print(f"{name}: no swap symmetry found")
        return 1

    x1 = next(s for s in S if skey(s)[0] != ident or skey(s)[1] != 0)
    for c in S:
        cinv = tuple(facs[i].inverse(c[0][i]) for i in range(nf))
        for t in S:
            target = tuple(facs[i].mul(t[0][i], cinv[i]) for i in range(nf))
            tz = (t[1] - c[1]) % n
            for r in rs:
                if (r * x1[1]) % n != tz:
                    continue
                cand = [facs[i].conj_solutions(x1[0][i], target[i]) for i in range(nf)]
                if not all(cand):
                    continue
                for gs in (np.array(np.meshgrid(*[np.arange(len(cnd)) for cnd in cand], indexing="ij")).reshape(nf, -1).T):
                    g = [cand[i][gs[i]] for i in range(nf)]
                    gi = [facs[i].inverse(g[i]) for i in range(nf)]

                    def beta(s):
                        m = tuple(facs[i].mul(facs[i].mul(facs[i].mul(g[i], s[0][i]), gi[i]), c[0][i]) for i in range(nf))
                        return (m, (r * s[1] + c[1]) % n)
                    if all(skey(beta(s)) in Sset for s in S):
                        cyc = cycles(beta)
                        if max(cyc) == 1:
                            continue
                        ce = skey(c)[0] == ident and skey(c)[1] == 0
                        print(f"{name}: S closed under beta(x) = alpha(x)*c, alpha = conj by {tuple('mat' + str(x) for x in g)} "
                              f"x (z -> {r}z mod {n}), c = {'e' if ce else c}; cycle sizes of beta on S: {cyc}")
                        return 0
    print(f"{name}: no symmetry of this form found")
    return 1


if __name__ == "__main__":
    sys.exit(main())
