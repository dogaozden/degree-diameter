#!/usr/bin/env python3
"""Card c2, squad conics-r1: independent check of CLAIM 1 and CLAIM 2 of BRIEF.md over GF(9) and GF(25).

Written from the brief's definitions only. Only the GF(q) arithmetic is imported (research/plus2/coords/coords.py).
Instances: q=9 (all u != -u, i.e. u != 0), q=25 (all u != 0); configs: three hats X_a=Z, three hats X_a=Z',
four hats (X_a=Z, X_c=Z'). Each instance passes iff both claims hold on it.
"""
import sys
import json
import itertools
from collections import Counter

sys.path.insert(0, '/home/user/degree-diameter/research/plus2/coords')
import coords  # noqa: E402  (GF class only)
import numpy as np  # noqa: E402

A_PT = (0, 1, 0)
Z = (1, 0, 0)
ZP = (0, 0, 1)
HERE = '/home/user/degree-diameter/research/squads/conics-r1/c2'


def make_field(q):
    F = coords.GF(q)
    E = range(q)
    for x in E:
        assert F.add(x, 0) == x and F.mul(x, 1) == x and F.mul(x, 0) == 0
        assert F.add(x, F.neg(x)) == 0
        if x:
            assert F.mul(x, F.inv(x)) == 1
        for y in E:
            assert F.add(x, y) == F.add(y, x) and F.mul(x, y) == F.mul(y, x)
            for z in E:
                assert F.add(F.add(x, y), z) == F.add(x, F.add(y, z))
                assert F.mul(F.mul(x, y), z) == F.mul(x, F.mul(y, z))
                assert F.mul(x, F.add(y, z)) == F.add(F.mul(x, y), F.mul(x, z))
    return F


class Plane:
    def __init__(self, q):
        self.q = q
        F = make_field(q)
        self.F = F
        self.add, self.mul, self.neg, self.inv = F.add, F.mul, F.neg, F.inv
        self.half = F.inv(F.add(1, 1))
        self.m2 = F.neg(F.add(1, 1))  # -2
        seen = set()
        for v in itertools.product(range(q), repeat=3):
            if any(v):
                seen.add(self.norm(v))
        self.PG = sorted(seen)
        assert len(self.PG) == q * q + q + 1
        # PG incidences (points as tuples, lines as tuples; same normalised-triple set)
        self.base = set()
        for p in self.PG:
            for L in self.PG:
                if self.dot(p, L) == 0:
                    self.base.add((('P', p), ('L', L)))
        # conic x z = y^2 and its polarity, sanity
        for p in self.PG:
            assert self.pole_ln(self.polar_pt(p)) == p
            on_conic = self.mul(p[0], p[2]) == self.mul(p[1], p[1])
            assert (self.dot(p, self.polar_pt(p)) == 0) == on_conic
        self.ell = self.polar_pt(A_PT)
        assert self.ell == (0, 1, 0), self.ell

    def norm(self, v):
        i = next(i for i in range(3) if v[i] != 0)
        s = self.inv(v[i])
        return tuple(self.mul(s, t) for t in v)

    def dot(self, p, L):
        return self.add(self.add(self.mul(p[0], L[0]), self.mul(p[1], L[1])), self.mul(p[2], L[2]))

    def polar_pt(self, p):  # point (x,y,z) -> line [z, -2y, x]
        return self.norm((p[2], self.mul(self.m2, p[1]), p[0]))

    def pole_ln(self, L):  # line [a,b,c] -> point (c, -b/2, a)
        return self.norm((L[2], self.mul(self.neg(L[1]), self.half), L[0]))

    def build(self, kind, xa, u):
        """Return the structure S: pts, lns, flags (set of (point, line) pairs), theta (dict)."""
        neg, dot, PG, ell = self.neg, self.dot, self.PG, self.ell
        if kind == 3:
            labels = ['0', '1', 'a']
            T = ['0', '1']
            pi = {'0': '1', '1': '0'}
            rho = {'0': '0', '1': '1'}  # identity ("no rotation")
            tau = {'0': '1', '1': '0', 'a': 'a'}
            X = {'a': Z if xa == 'Z' else ZP, '0': (1, 0, u), '1': (1, 0, neg(u))}
        else:
            assert xa == 'Z'
            labels = ['0', '1', 'a', 'c']
            T = ['0', 'c', '1']
            sigma = {'0': 'c', 'c': '1', '1': '0'}
            pi = sigma
            rho = sigma
            tau = {'0': '1', '1': '0', 'a': 'a', 'c': 'c'}
            X = {'a': Z, '0': (1, 0, u), '1': (1, 0, neg(u)), 'c': ZP}
        assert len(set(X.values())) == len(labels)
        for s in labels:
            assert dot(X[s], ell) == 0  # marked points lie on ell
        lam = {}
        for s in labels:
            c = [L for L in PG if dot(A_PT, L) == 0 and dot(X[s], L) == 0]
            assert len(c) == 1
            lam[s] = c[0]  # lam_s = A X_s

        flags = set(self.base)
        # (R1) delete (X_s, lam_s), s in S; add (X_t, lam_rho(t)), t in T
        for s in labels:
            flags.discard((('P', X[s]), ('L', lam[s])))
        for t in T:
            flags.add((('P', X[t]), ('L', lam[rho[t]])))
        # (R2) H_s on every (PG) line through X_s other than ell
        for s in labels:
            for L in PG:
                if L != ell and dot(X[s], L) == 0:
                    flags.add((('H', s), ('L', L)))
        # (R3) K_s contains every point of lam_s other than A
        for s in labels:
            for p in PG:
                if p != A_PT and dot(p, lam[s]) == 0:
                    flags.add((('P', p), ('K', s)))
        # (R4) M contains the points of ell* (= ell minus X_t, t in T) and every H_s
        Xt = [X[t] for t in T]
        for p in PG:
            if dot(p, ell) == 0 and p not in Xt:
                flags.add((('P', p), ('M',)))
        for s in labels:
            flags.add((('H', s), ('M',)))
        # (R5) Q on the lines of Lam* (lines through A other than lam_t, t in T) and on every K_s
        lamt = [lam[t] for t in T]
        for L in PG:
            if dot(A_PT, L) == 0 and L not in lamt:
                flags.add((('Q',), ('L', L)))
        for s in labels:
            flags.add((('Q',), ('K', s)))
        # (R6) A on K_a; H_a on ell; H_t on K_pi(t) for t in T
        flags.add((('P', A_PT), ('K', 'a')))
        flags.add((('H', 'a'), ('L', ell)))
        for t in T:
            flags.add((('H', t), ('K', pi[t])))

        pts = [('P', p) for p in PG] + [('Q',)] + [('H', s) for s in labels]
        lns = [('L', L) for L in PG] + [('M',)] + [('K', s) for s in labels]
        pset, lset = set(pts), set(lns)
        for (p, L) in flags:
            assert p in pset and L in lset, (p, L)

        def theta(x):
            k = x[0]
            if k == 'P':
                return ('L', self.polar_pt(x[1]))
            if k == 'L':
                return ('P', self.pole_ln(x[1]))
            if k == 'H':
                return ('K', tau[x[1]])
            if k == 'K':
                return ('H', tau[x[1]])
            if k == 'Q':
                return ('M',)
            if k == 'M':
                return ('Q',)
            raise ValueError(x)

        th = {x: theta(x) for x in pts + lns}
        return dict(kind=kind, labels=labels, pts=pts, lns=lns, flags=flags, theta=th,
                    lam=lam, X=X, expect_n=self.q * self.q + self.q + (5 if kind == 3 else 6))


def claim1(q, S):
    pts, lns, flags, th = S['pts'], S['lns'], S['flags'], S['theta']
    res = {}
    # theta: points -> lines, lines -> points, bijective, involutive
    res['theta_bijective_types'] = (set(th[p] for p in pts) == set(lns)) and (set(th[L] for L in lns) == set(pts))
    res['theta_involutive'] = all(th[th[x]] == x for x in pts + lns)
    # flags to flags: (p,L) flag iff (theta(L), theta(p)) flag
    res['flags_to_flags'] = all(((p, L) in flags) == ((th[L], th[p]) in flags) for p in pts for L in lns)
    # degrees
    deg = Counter()
    for (p, L) in flags:
        deg[p] += 1
        deg[L] += 1
    degs = [deg[x] for x in pts + lns]
    res['max_deg'] = max(degs)
    res['deg_le_q2'] = max(degs) <= q + 2
    res['max_deg_eq_q2'] = max(degs) == q + 2
    deficient = Counter()
    for x in pts + lns:
        if deg[x] == q + 1:
            deficient[('point' if x[0] in ('P', 'H', 'Q') else 'line') + ':' + x[0]] += 1
    res['deficient_by_type'] = dict(deficient)
    # diameter of incidence graph
    n_p = len(pts)
    idx = {x: i for i, x in enumerate(pts + lns)}
    n = len(idx)
    R = np.eye(n, dtype=np.float32)
    for (p, L) in flags:
        R[idx[p], idx[L]] = 1
        R[idx[L], idx[p]] = 1
    P2 = (R @ R > 0).astype(np.float32)
    P3 = (P2 @ R > 0)
    res['points_collinear'] = bool(P2[:n_p, :n_p].all())
    res['lines_concurrent'] = bool(P2[n_p:, n_p:].all())
    res['diam_le3'] = bool(P3.all())  # point-line non-incident pairs are at distance exactly 3 (odd, not 1)
    res['pass'] = (res['theta_bijective_types'] and res['theta_involutive'] and res['flags_to_flags']
                   and res['max_deg_eq_q2'] and res['deg_le_q2'] and res['points_collinear']
                   and res['lines_concurrent'] and res['diam_le3'])
    return res


def claim2(q, S):
    pts, flags, th = S['pts'], S['flags'], S['theta']
    res = {}
    n = len(pts)
    pts_on = {}
    for (p, L) in flags:
        pts_on.setdefault(L, set()).add(p)
    adj = np.zeros((n, n), dtype=bool)
    for j, pj in enumerate(pts):
        line = th[pj]
        on = pts_on.get(line, set())
        for i, pi_ in enumerate(pts):
            if i != j and pi_ in on:  # p_i ~ p_j iff p_i != p_j and p_i lies on theta(p_j)
                adj[i, j] = True
    res['n_vertices'] = n
    res['n_expected'] = S['expect_n']
    res['symmetric'] = bool(np.array_equal(adj, adj.T))
    res['no_loops'] = not bool(np.any(np.diag(adj)))
    deg = adj.sum(axis=1)
    res['max_deg'] = int(deg.max())
    res['max_deg_eq_q2'] = int(deg.max()) == q + 2
    R = (adj | np.eye(n, dtype=bool)).astype(np.float32)
    P2 = (R @ R > 0)
    res['diam_le2'] = bool(P2.all())
    res['diam2_exact'] = res['diam_le2'] and int(adj.sum()) < n * (n - 1)
    res['pass'] = (res['symmetric'] and res['no_loops'] and res['max_deg_eq_q2'] and res['diam_le2']
                   and res['n_vertices'] == res['n_expected'])
    return res


def main():
    out = []
    for q in (9, 25):
        P = Plane(q)
        F = P.F
        us = [u for u in range(q) if u != 0 and F.neg(u) != u]
        assert len(us) == q - 1  # char odd: u != -u  <=>  u != 0
        for u in us:
            for kind, xa in ((3, 'Z'), (4, 'Z'), (3, 'Zp')):
                S = P.build(kind, xa, u)
                c1 = claim1(q, S)
                c2 = claim2(q, S)
                inst = dict(q=q, u=u, kind=kind, xa=xa, claim1=c1, claim2=c2,
                            pass_=bool(c1['pass'] and c2['pass']))
                out.append(inst)
                print(f"q={q:2d} u={u:2d} hats={kind} Xa={xa:2s} | C1 pass={c1['pass']} "
                      f"(inv={c1['theta_involutive']} f2f={c1['flags_to_flags']} maxdeg={c1['max_deg']} "
                      f"coll={c1['points_collinear']} conc={c1['lines_concurrent']} diam3={c1['diam_le3']} "
                      f"def={c1['deficient_by_type']}) | C2 pass={c2['pass']} "
                      f"(n={c2['n_vertices']} sym={c2['symmetric']} maxdeg={c2['max_deg']} "
                      f"diam<=2={c2['diam_le2']} exact2={c2['diam2_exact']})", flush=True)
    score = sum(1 for r in out if r['pass_'])
    valid = score == len(out)
    summary = dict(score=score, total=len(out), valid=valid)
    print('SUMMARY', json.dumps(summary))
    with open(HERE + '/results.json', 'w') as fh:
        json.dump(dict(summary=summary, instances=out), fh, indent=1, default=str)
    return summary


if __name__ == '__main__':
    main()
