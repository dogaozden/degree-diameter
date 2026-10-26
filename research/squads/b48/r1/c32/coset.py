# Coset graphs Cos(G; A, B) for G = Z_m x|_u Z_4 (elements (t,k), (t,k)(t',k') = (t+u^k t', k+k')),
# A = <(0,1)>, B = conjugate of A by (c,0). Vertices: left cosets xA (indexed by t, side 1) and xB (side 2).
# Edge set: one edge per group element x: (xA, xB). Degree 4 iff A cap B = 1.
# Base vertices: side-1 coset A (id 0) and side-2 coset B (id m). G is transitive on each side, so the
# eccentricities of these two vertices determine the diameter.
import sys
from collections import deque

def analyse(m, u, c, want_edges=False):
    pw = [1, u % m, (u * u) % m, (u ** 3) % m]
    # B = {(c(1-u^k), k)}; check A cap B = 1
    Bel = [((c * (1 - pw[k])) % m, k) for k in range(4)]
    if any(Bel[k][0] == 0 for k in range(1, 4)):
        return None
    def mul(x, y):
        return ((x[0] + pw[x[1]] * y[0]) % m, (x[1] + y[1]) % 4)
    # side-2 coset id: canonical rep = min over x*B
    key2 = {}
    id2 = {}
    for t in range(m):
        for k in range(4):
            x = (t, k)
            rep = min(mul(x, b) for b in Bel)
            if rep not in id2:
                id2[rep] = len(id2)
            key2[x] = id2[rep]
    if len(id2) != m:
        return None
    edges = set()
    for t in range(m):
        for k in range(4):
            e = (t, m + key2[(t, k)])
            if e in edges:
                return None
            edges.add(e)
    n = 2 * m
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    if any(len(l) != 4 for l in adj):
        return None
    def far(src):
        dist = [-1] * n
        dist[src] = 0
        dq = deque([src])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v] + 1
                    dq.append(w)
        if min(dist) < 0:
            return 10 ** 9, 10 ** 9
        return sum(1 for d in dist if d > 8), max(dist)
    f0, d0 = far(0)
    f1, d1 = far(m)
    res = dict(m=m, u=u, c=c, n=n, cost=f0 + f1, miss=(f0 + f1) / m, ecc=max(d0, d1))
    if want_edges:
        res['edges'] = sorted(edges)
    return res

if __name__ == '__main__':
    lo, hi = int(sys.argv[1]), int(sys.argv[2])
    out = open(sys.argv[3], 'w')
    best = []
    for m in range(lo, hi + 1):
        us = [u for u in range(2, m) if pow(u, 4, m) == 1 and pow(u, 2, m) != 1]
        for u in us:
            for c in range(1, m):
                if m % c:
                    continue  # orbit reps under unit scaling: c | m
                if c == m:
                    continue
                r = analyse(m, u, c)
                if r is None:
                    continue
                out.write('m=%d u=%d c=%d n=%d cost=%d miss=%.4f ecc=%d\n' % (m, u, c, r['n'], r['cost'], r['miss'], r['ecc']))
                best.append((r['cost'], m, u, c, r['n'], r['ecc']))
    best.sort()
    print('count', len(best))
    for b in best[:15]:
        print('cost=%d m=%d u=%d c=%d n=%d ecc=%d' % b)
