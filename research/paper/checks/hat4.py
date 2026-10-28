# Spot check of Section 3 of joint.tex, written from the paper's Definition 3.1 and Table 2 (prime q only).
import sys, itertools
from collections import deque

def norm(v, q):
    for c in v:
        if c % q:
            inv = pow(c, q - 2, q)
            return tuple(x * inv % q for x in v)
    raise ValueError

def run(q, a, c):
    F = range(q)
    pts = sorted({norm(v, q) for v in itertools.product(F, repeat=3) if any(v)})
    lines = pts[:]  # [u:v:w] as normalised triples
    inc = lambda p, L: (p[0]*L[0] + p[1]*L[1] + p[2]*L[2]) % q == 0
    X = lambda t: norm((0, t, 1), q); P = (0, 1, 0); A = (1, 0, 0)
    ell = (1, 0, 0); lam = lambda t: norm((0, 1, -t % q), q); laminf = (0, 0, 1)
    S = [0, 1, a, c]; T = [0, 1, c]; sig = {0: c, c: 1, 1: 0}
    E = set()
    for p in pts:
        for L in lines:
            if inc(p, L): E.add((('p', p), ('l', L)))
    for s in S: E.discard((('p', X(s)), ('l', lam(s))))
    for t in T: E.add((('p', X(t)), ('l', lam(sig[t]))))
    for s in S:
        for w in F: E.add((('p', 'H%d' % s), ('l', norm((w, 1, -s % q), q))))
        for x in F: E.add((('p', norm((x, s, 1), q)), ('l', 'K%d' % s)))
    E.add((('p', P), ('l', 'M')))
    for t in F:
        if t not in T: E.add((('p', X(t)), ('l', 'M')))
    for s in S: E.add((('p', 'H%d' % s), ('l', 'M')))
    E.add((('p', 'Q'), ('l', laminf)))
    for t in F:
        if t not in T: E.add((('p', 'Q'), ('l', lam(t))))
    for s in S: E.add((('p', 'Q'), ('l', 'K%d' % s)))
    E.add((('p', A), ('l', 'K%d' % a))); E.add((('p', 'H%d' % a), ('l', ell)))
    for t in T: E.add((('p', 'H%d' % t), ('l', 'K%d' % sig[t])))
    adj = {}
    for u, v in E:
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    n = len(adj)
    assert n == 2 * (q * q + q + 6), n
    degs = sorted(len(x) for x in adj.values())
    assert max(degs) == q + 2
    defic = [v for v in adj if len(adj[v]) == q + 1]
    assert len(defic) == 2 * (q - 1) * (q - 3), len(defic)
    # filler: (x:y:1)~[x:1:-y] (x!=0, y not in S); (x:1:0)~[1:0:-1/x]
    E2 = set(E)
    for x in range(1, q):
        for y in F:
            if y not in S: E2.add((('p', norm((x, y, 1), q)), ('l', norm((x, 1, -y % q), q))))
        E2.add((('p', norm((x, 1, 0), q)), ('l', norm((1, 0, -pow(x, q - 2, q) % q), q))))
    adj2 = {}
    for u, v in E2:
        adj2.setdefault(u, set()).add(v); adj2.setdefault(v, set()).add(u)
    assert all(len(x) == q + 2 for x in adj2.values()) and len(E2) == len(E) + (q - 1) * (q - 3)
    def diam(adj):
        best = 0
        for s in adj:
            dist = {s: 0}; dq = deque([s])
            while dq:
                u = dq.popleft()
                for w in adj[u]:
                    if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
            assert len(dist) == len(adj)
            best = max(best, max(dist.values()))
        return best
    # a few rows of Table 2: degrees of (x:y:1), [u:1:w]
    for x in range(1, q):
        for y in F:
            d = len(adj[('p', norm((x, y, 1), q))]); assert d == (q + 2 if y in S else q + 1)
    return diam(adj), diam(adj2)

for q in [5, 7, 11]:
    for a in range(2, q):
        for c in range(2, q):
            if a != c and (q < 11 or (a, c) == (2, 3)):
                dG, dR = run(q, a, c)
                assert dG == 3 and dR == 3, (q, a, c, dG, dR)
    print("q =", q, "ok: order", 2 * (q * q + q + 6), "G and R diameter 3, R regular")
