#!/usr/bin/env python3
"""Card c4 (conics-r1): negative controls for the conic polarity theta on the hat structure S.

Self-written from BRIEF.md and Definition 1.1 (R1)-(R6) of SYNTHETIC.md. Does not import research/synthetic/conics.
Frames: marked points X_s on ell (y = 0) are ANY distinct points of ell, not only the conic-adapted ones.
For each frame: build S, check theta (old point -> polar line, old line -> pole, H_s -> K_tau(s), K_s -> H_tau(s),
Q <-> M) is an involution and maps flags to flags, and compute the diameter of the incidence graph.
Writes results.json next to this file and prints a summary.
"""
import itertools
import json
import os
from collections import deque

HERE = os.path.dirname(os.path.abspath(__file__))


class Plane:
    def __init__(self, q):
        self.q = q
        allp = set()
        for v in itertools.product(range(q), repeat=3):
            if any(v):
                allp.add(self.norm(v))
        self.pts = sorted(allp)
        self.idx = {p: i for i, p in enumerate(self.pts)}
        self.N = len(self.pts)
        assert self.N == q * q + q + 1
        self.inv2 = pow(2, q - 2, q)

    def norm(self, v):
        q = self.q
        v = tuple(x % q for x in v)
        for x in v:
            if x:
                i = pow(x, q - 2, q)
                return tuple((y * i) % q for y in v)
        raise ValueError("zero vector")

    def dot(self, u, v):
        return sum(a * b for a, b in zip(u, v)) % self.q

    def cross(self, u, v):
        return (u[1] * v[2] - u[2] * v[1], u[2] * v[0] - u[0] * v[2], u[0] * v[1] - u[1] * v[0])

    # conic x z = y^2: point (x,y,z) -> line [z,-2y,x]; line [a,b,c] -> point (c,-b/2,a)
    def polar_pt(self, p):
        x, y, z = p
        return self.norm((z, -2 * y, x))

    def pole_ln(self, L):
        a, b, c = L
        return self.norm((c, -b * self.inv2, a))


def build(P, Xs, four):
    """Return (points, lines, inc) for the structure S with marked points Xs (label -> normalized point)."""
    if four:
        S = ['0', '1', 'a', 'c']
        T = ['0', 'c', '1']
        sig = {'0': 'c', 'c': '1', '1': '0'}
        pi = dict(sig)
        rho = dict(sig)
    else:
        S = ['0', '1', 'a']
        T = ['0', '1']
        pi = {'0': '1', '1': '0'}
        rho = {'0': '0', '1': '1'}
    tau = {'0': '1', '1': '0', 'a': 'a', 'c': 'c'}

    A = P.norm((0, 1, 0))
    Ai = P.idx[A]
    ell = P.norm((0, 1, 0))  # line y = 0
    elli = P.idx[ell]
    X = {s: P.idx[Xs[s]] for s in S}
    lam = {s: P.idx[P.norm(P.cross(A, Xs[s]))] for s in S}  # lam_s = A X_s
    for s in S:
        assert P.dot(P.pts[X[s]], ell) == 0
        assert P.dot(A, P.pts[lam[s]]) == 0 and P.dot(P.pts[X[s]], P.pts[lam[s]]) == 0

    # R1: old incidences, minus (X_s, lam_s) for s in S, plus (X_t, lam_rho(t)) for t in T
    inc = set(P._base_flags)
    for s in S:
        inc.discard((('p', X[s]), ('l', lam[s])))
    for t in T:
        inc.add((('p', X[t]), ('l', lam[rho[t]])))

    # ell* = points of ell other than X_t (t in T); Lam* = lines through A other than lam_t (t in T)
    ell_pts = [i for i, p in enumerate(P.pts) if P.dot(p, ell) == 0]
    XT = {X[t] for t in T}
    ellstar = [i for i in ell_pts if i not in XT]
    lamT = {lam[t] for t in T}
    Lam = [j for j, L in enumerate(P.pts) if P.dot(A, L) == 0]
    Lamstar = [j for j in Lam if j not in lamT]

    # R2: H_s on every old line through X_s other than ell
    for s in S:
        Xp = P.pts[X[s]]
        for j, L in enumerate(P.pts):
            if j != elli and P.dot(Xp, L) == 0:
                inc.add((('H', s), ('l', j)))
    # R3: K_s contains every old point of lam_s other than A
    for s in S:
        Ls = P.pts[lam[s]]
        for i, p in enumerate(P.pts):
            if i != Ai and P.dot(p, Ls) == 0:
                inc.add((('p', i), ('K', s)))
    # R4: M contains ell* and every H_s
    for i in ellstar:
        inc.add((('p', i), ('M',)))
    for s in S:
        inc.add((('H', s), ('M',)))
    # R5: Q on the lines of Lam* and on every K_s
    for j in Lamstar:
        inc.add((('Q',), ('l', j)))
    for s in S:
        inc.add((('Q',), ('K', s)))
    # R6: A on K_a; H_a on ell; H_t on K_pi(t)
    inc.add((('p', Ai), ('K', 'a')))
    inc.add((('H', 'a'), ('l', elli)))
    for t in T:
        inc.add((('H', t), ('K', pi[t])))

    points = [('p', i) for i in range(P.N)] + [('Q',)] + [('H', s) for s in S]
    lines = [('l', j) for j in range(P.N)] + [('M',)] + [('K', s) for s in S]
    return S, tau, points, lines, inc


def theta_factory(P, tau):
    cache = {}

    def theta(x):
        if x in cache:
            return cache[x]
        k = x[0]
        if k == 'p':
            y = ('l', P.idx[P.polar_pt(P.pts[x[1]])])
        elif k == 'l':
            y = ('p', P.idx[P.pole_ln(P.pts[x[1]])])
        elif k == 'H':
            y = ('K', tau[x[1]])
        elif k == 'K':
            y = ('H', tau[x[1]])
        elif k == 'Q':
            y = ('M',)
        elif k == 'M':
            y = ('Q',)
        else:
            raise KeyError(x)
        cache[x] = y
        return y
    return theta


def diameter(nodes, inc):
    index = {v: i for i, v in enumerate(nodes)}
    n = len(nodes)
    adj = [0] * n
    for (p, L) in inc:
        a, b = index[p], index[L]
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    full = (1 << n) - 1
    diam = 0
    for s in range(n):
        seen = 1 << s
        frontier = seen
        d = 0
        while True:
            nxt = 0
            f = frontier
            while f:
                low = f & -f
                nxt |= adj[low.bit_length() - 1]
                f ^= low
            nxt &= ~seen
            if not nxt:
                break
            d += 1
            seen |= nxt
            frontier = nxt
        if seen != full:
            return None  # disconnected
        diam = max(diam, d)
    return diam


def check_polarity(P, S, tau, points, lines, inc):
    theta = theta_factory(P, tau)
    pset = set(points)
    lset = set(lines)
    # theta maps points to lines and lines to points
    for x in points:
        assert theta(x) in lset, x
    for L in lines:
        assert theta(L) in pset, L
    involutive = all(theta(theta(x)) == x for x in points + lines)
    mism = []
    for x in points:
        tx = theta(x)
        for L in lines:
            a = (x, L) in inc
            b = (theta(L), tx) in inc
            if a != b:
                mism.append((x, L))
    return involutive, mism


def name_pt(P, x):
    return str(P.pts[x[1]]) if x[0] == 'p' else x[0]


def run(q):
    P = Plane(q)
    ell = P.norm((0, 1, 0))
    P._base_flags = set()
    for i, p in enumerate(P.pts):
        for j, L in enumerate(P.pts):
            if P.dot(p, L) == 0:
                P._base_flags.add((('p', i), ('l', j)))
    ell_pts = [p for p in P.pts if P.dot(p, ell) == 0]
    assert len(ell_pts) == q + 1
    Z = P.norm((1, 0, 0))
    Zp = P.norm((0, 0, 1))

    def conj(X):  # the point of ell on the polar of X (conjugate on ell)
        pol = P.polar_pt(X)
        cands = [Y for Y in ell_pts if P.dot(Y, pol) == 0]
        assert len(cands) == 1
        return cands[0]

    results = {}
    for four in (False, True):
        key = 'four' if four else 'three'
        labels = ['a', 'c', '0', '1'] if four else ['a', '0', '1']
        passing, predicted_set, total, diam_bad, invol_bad = [], set(), 0, [], 0
        mism_counts = {}
        for tup in itertools.permutations(ell_pts, len(labels)):
            Xs = dict(zip(labels, tup))
            total += 1
            S, tau, points, lines, inc = build(P, Xs, four)
            invol, mism = check_polarity(P, S, tau, points, lines, inc)
            ok = invol and not mism
            if not invol:
                invol_bad += 1
            if mism:
                mism_counts[len(mism)] = mism_counts.get(len(mism), 0) + 1
            if ok:
                passing.append(tup)
            # prediction: {Xa,Xc} = {Z,Z'} (four) / Xa in {Z,Z'} (three), X_1 = conj(X_0)
            if four:
                pred = ({Xs['a'], Xs['c']} == {Z, Zp}) and (Xs['1'] == conj(Xs['0']))
            else:
                pred = (Xs['a'] in (Z, Zp)) and (Xs['1'] == conj(Xs['0']))
            if pred:
                predicted_set.add(tup)
            d = diameter(points + lines, inc)
            if d != 3:
                diam_bad.append((tup, d))
        passset = set(passing)
        results[key] = {
            'q': q,
            'frames_tested': total,
            'passing': len(passing),
            'predicted': len(predicted_set),
            'passing_equals_predicted': passset == predicted_set,
            'passing_minus_predicted': len(passset - predicted_set),
            'predicted_minus_passing': len(predicted_set - passset),
            'involution_failures': invol_bad,
            'mismatch_count_histogram': {str(k): v for k, v in sorted(mism_counts.items())},
            'frames_with_diameter_not_3': len(diam_bad),
            'passing_frames': [
                {'labels': {l: str(P.pts[Xs_i]) for l, Xs_i in zip(labels, [P.idx[t] for t in tup])}}
                for tup in passing
            ],
        }
        print(key, 'q=%d' % q, 'tested', total, 'passing', len(passing), 'predicted', len(predicted_set),
              'match', passset == predicted_set, 'diam!=3', len(diam_bad), 'invol_fail', invol_bad,
              'mismatch hist', dict(sorted(mism_counts.items())))
        for tup in passing:
            print('   pass', labels, [str(t) for t in tup])
    return results


if __name__ == '__main__':
    allres = {}
    for q in (5, 7):
        allres['q%d' % q] = run(q)
    total = sum(r['frames_tested'] for q in allres.values() for r in q.values())
    valid = all(r['passing_equals_predicted'] for q in allres.values() for r in q.values())
    diam_ok = all(r['frames_with_diameter_not_3'] == 0 for q in allres.values() for r in q.values())
    out = {'score': total, 'valid': valid, 'all_diameter_3': diam_ok, 'results': allres}
    with open(os.path.join(HERE, 'results.json'), 'w') as f:
        json.dump(out, f, indent=1)
    print('TOTAL frames', total, 'valid', valid, 'all diameter 3', diam_ok)
