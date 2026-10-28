# Spot check of Theorem 4.7 / Corollary 4.8 of joint.tex from the paper's coordinates (prime q).
from collections import deque
import itertools

def run(q):
    inv = lambda x: pow(x, q - 2, q)
    sq = {x * x % q for x in range(1, q)}
    eps = next(x for x in range(2, q) if x not in sq)
    N = lambda b, c: (b * b - eps * c * c) % q
    pts = [(a, b, c) for a in range(q) for b in range(q) for c in range(q)]
    lines = []
    for b0 in range(q):
        for c0 in range(q):
            lines.append(frozenset(((m) % q, b0, c0) for m in range(q)))  # fibre over (b0,c0)
    dirs = [(0, 1)] + [(1, t) for t in range(q)]
    seen = set()
    for (a0, b0, c0) in pts:
        for (d1, d2) in dirs:
            rho = (b0 * d2 - c0 * d1) % q
            L = frozenset(((a0 + l * rho) % q, (b0 + l * d1) % q, (c0 + l * d2) % q) for l in range(q))
            if L not in seen: seen.add(L)
    lines += list(seen)
    assert len(lines) == q * q + q * q * (q + 1), len(lines)
    # GQ order (q-1,q+1): every point on q+2 lines; GQ axiom
    on = {p: [] for p in pts}
    for i, L in enumerate(lines):
        assert len(L) == q
        for p in L: on[p].append(i)
    assert all(len(v) == q + 2 for v in on.values())
    k1 = inv(2); k2 = inv(2 * eps % q)
    E1 = {(k1 * N(b, c) % q, b, c) for b in range(q) for c in range(q)}
    E2 = {(k2 * N(b, c) % q, b, c) for b in range(q) for c in range(q)}
    assert E1 & E2 == {(0, 0, 0)}
    for L in lines:
        assert len(L & E1) + len(L & E2) == 2
    # Corollary 4.8 graph
    adj = {}
    def add(u, v):
        adj.setdefault(u, set()).add(v); adj.setdefault(v, set()).add(u)
    for i, L in enumerate(lines):
        for p in L:
            add(('p', p), ('l', i))
            if p in E1: add(('c1', p), ('l', i))
            if p in E2: add(('c2', p), ('l', i))
    n = len(adj)
    assert n == 2 * q * q * (q + 2), n
    assert all(len(v) == q + 2 for v in adj.values())
    best = 0
    for s in adj:
        dist = {s: 0}; dq = deque([s])
        while dq:
            u = dq.popleft()
            for w in adj[u]:
                if w not in dist: dist[w] = dist[u] + 1; dq.append(w)
        assert len(dist) == n
        best = max(best, max(dist.values()))
    return n, best

for q in [3, 5, 7]:
    print(q, run(q))
