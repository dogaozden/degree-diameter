"""Referee check of Definition 3.1 / Table 2 / Theorem 3.2 (fourth hat), built from (C1)-(C6) as printed."""
import sys, itertools
from collections import deque
from gf import GF

def norm(F, v):
    for c in v:
        if c:
            ic = F.inv[c]; return tuple(F.mul[ic][x] for x in v)
    raise ValueError

def build(q, a, c, filler=True, rotation=True, link_H1K0=True):
    F = GF(q); E = list(F.elts()); M = F.mul; A_ = F.add; neg = F.neg
    pts = set(norm(F, v) for v in itertools.product(E, repeat=3) if any(v))
    lines = sorted(pts)
    pts = sorted(pts)
    inc = lambda p, L: A_[A_[M[L[0]][p[0]]][M[L[1]][p[1]]]][M[L[2]][p[2]]] == 0
    X = lambda t: norm(F, (0, t, 1)); P = (0, 1, 0); Apt = (1, 0, 0)
    lam = lambda t: norm(F, (0, 1, neg[t])); laminf = (0, 0, 1); ell = (1, 0, 0)
    S = [0, 1, a, c]; T = [0, 1, c]; sigma = {0: c, c: 1, 1: 0}
    adj = {}
    def addE(u, v):
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    Ppts = [('p', p) for p in pts]; Plin = [('L', L) for L in lines]
    for p in pts:
        for L in lines:
            if inc(p, L):
                if any(p == X(s) and L == lam(s) for s in S):
                    continue
                addE(('p', p), ('L', L))
    if rotation:
        for t in T:
            addE(('p', X(t)), ('L', lam(sigma[t])))
    for s in S:
        for w in E:   # (C2)
            addE(('H', s), ('L', norm(F, (w, 1, neg[s]))))
        for x in E:   # (C3)
            addE(('K', s), ('p', norm(F, (x, s, 1))))
    # (C4) M
    addE(('M',), ('p', P))
    for t in E:
        if t not in T: addE(('M',), ('p', X(t)))
    for s in S: addE(('M',), ('H', s))
    # (C5) Q
    addE(('Q',), ('L', laminf))
    for t in E:
        if t not in T: addE(('Q',), ('L', lam(t)))
    for s in S: addE(('Q',), ('K', s))
    # (C6) links
    addE(('p', Apt), ('K', a)); addE(('H', a), ('L', ell))
    for t in T:
        if t == 1 and not link_H1K0: continue
        addE(('H', t), ('K', sigma[t]))
    if filler:
        for x in E:
            if x == 0: continue
            for y in E:
                if y in S: continue
                u, v = ('p', norm(F, (x, y, 1))), ('L', norm(F, (x, 1, neg[y])))
                assert v not in adj[u]; addE(u, v)
            u, v = ('p', norm(F, (x, 1, 0))), ('L', norm(F, (1, 0, neg[F.inv[x]])))
            assert v not in adj[u]; addE(u, v)
    return F, adj

def diameter(adj):
    D = 0
    for s in adj:
        dist = {s: 0}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for v in adj[u]:
                if v not in dist: dist[v] = dist[u] + 1; dq.append(v)
        if len(dist) < len(adj): return None
        D = max(D, max(dist.values()))
    return D

def bip(adj):
    pts = lambda v: v[0] in ('p', 'H', 'Q')
    return all(pts(u) != pts(v) for u in adj for v in adj[u])

def table2(F, q, a, c):
    """Neighbourhoods as printed in Table 2, to compare with the build without filler."""
    E = list(F.elts()); M, A_, neg, inv = F.mul, F.add, F.neg, F.inv
    n = lambda v: norm(F, v)
    S = [0, 1, a, c]; T = [0, 1, c]; sig = {0: c, c: 1, 1: 0}; sinv = {v: k for k, v in sig.items()}
    X = lambda t: ('p', n((0, t, 1))); lam = lambda t: ('L', n((0, 1, neg[t])))
    tab = {}
    tab[('Q',)] = {('L', (0, 0, 1))} | {lam(t) for t in E if t not in T} | {('K', s) for s in S}
    tab[('H', a)] = {('L', n((w, 1, neg[a]))) for w in E} | {('M',), ('L', (1, 0, 0))}
    for t in T: tab[('H', t)] = {('L', n((w, 1, neg[t]))) for w in E} | {('M',), ('K', sig[t])}
    tab[('M',)] = {('p', (0, 1, 0))} | {X(t) for t in E if t not in T} | {('H', s) for s in S}
    tab[('K', a)] = {('p', n((x, a, 1))) for x in E} | {('Q',), ('p', (1, 0, 0))}
    for t in T: tab[('K', t)] = {('p', n((x, t, 1))) for x in E} | {('Q',), ('H', sinv[t])}
    tab[('p', (1, 0, 0))] = {lam(t) for t in E} | {('L', (0, 0, 1)), ('K', a)}
    tab[('p', (0, 1, 0))] = {('L', (1, 0, 0)), ('L', (0, 0, 1))} | {('L', n((1, 0, w))) for w in E if w} | {('M',)}
    for t in E:
        if t not in S: tab[X(t)] = {('L', (1, 0, 0))} | {('L', n((w, 1, neg[t]))) for w in E} | {('M',)}
    tab[X(a)] = {('L', (1, 0, 0))} | {('L', n((w, 1, neg[a]))) for w in E if w} | {('M',), ('K', a)}
    for t in T: tab[X(t)] = {('L', (1, 0, 0))} | {('L', n((w, 1, neg[t]))) for w in E if w} | {lam(sig[t]), ('K', t)}
    for x in E:
        if x == 0: continue
        for y in E:
            s = {('L', n((u, 1, neg[A_[M[u][x]][y]]))) for u in E} | {('L', n((1, 0, neg[x])))}
            if y in S: s.add(('K', y))
            tab[('p', n((x, y, 1)))] = s
        tab[('p', n((x, 1, 0)))] = {('L', (0, 0, 1))} | {('L', n((1, neg[x], w))) for w in E}
    tab[('L', (1, 0, 0))] = {('p', (0, 1, 0))} | {X(t) for t in E} | {('H', a)}
    tab[('L', (0, 0, 1))] = {('p', (1, 0, 0))} | {('p', n((x, 1, 0))) for x in E} | {('Q',)}
    for t in E:
        if t not in S: tab[lam(t)] = {('p', (1, 0, 0))} | {('p', n((x, t, 1))) for x in E} | {('Q',)}
    tab[lam(a)] = {('p', (1, 0, 0))} | {('p', n((x, a, 1))) for x in E if x} | {('Q',), ('H', a)}
    for t in T: tab[lam(t)] = {('p', (1, 0, 0))} | {('p', n((x, t, 1))) for x in E if x} | {X(sinv[t]), ('H', t)}
    for u in E:
        if u == 0: continue
        for w in E:
            s = {('p', n((x, neg[A_[M[u][x]][w]], 1))) for x in E} | {('p', n((neg[inv[u]], 1, 0)))}
            if neg[w] in S: s.add(('H', neg[w]))
            tab[('L', n((u, 1, w)))] = s
    for w in E:
        if w: tab[('L', n((1, 0, w)))] = {('p', n((neg[w], y, 1))) for y in E} | {('p', (0, 1, 0))}
    return tab

if __name__ == '__main__':
    for q in [4, 5, 7, 8, 9, 11, 13]:
        F = GF(q)
        pairs = [(a, c) for a in range(2, q) for c in range(2, q) if a != c]
        if q > 9: pairs = pairs[:3]
        for (a, c) in pairs:
            F, G = build(q, a, c, filler=False)
            tab = table2(F, q, a, c)
            assert set(tab) == set(G), (q, a, c, len(tab), len(G))
            bad = [v for v in G if G[v] != tab[v]]
            assert not bad, (q, a, c, bad[:2])
            dG = diameter(G); degs = sorted(set(len(G[v]) for v in G))
            F, R = build(q, a, c, filler=True)
            dR = diameter(R); degsR = sorted(set(len(R[v]) for v in R))
            assert len(G) == 2 * (q*q + q + 6) and dG == 3 and dR == 3 and degs[-1] == q + 2 and degsR == [q + 2] and bip(G) and bip(R)
        # necessity remarks: no rotation / no link H1-K0
        a, c = pairs[0]
        d1 = diameter(build(q, a, c, filler=False, rotation=False)[1])
        d2 = diameter(build(q, a, c, filler=False, link_H1K0=False)[1])
        print(f"q={q}: {len(pairs)} (a,c) pairs ok: Table 2 rows equal (C1)-(C6), |V|={2*(q*q+q+6)}, diam G=R=3, R {q+2}-regular;"
              f" without rotation diam={d1}, without H1~K0 diam={d2}")
