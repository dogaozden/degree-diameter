# Generic coset graphs Cos(G; A, B) for a permutation group G, |A| = |B| = 4, A cap B = 1.
# Edge per group element x: (xA, xB). Side sizes N/4, n = N/2. Base vertices: coset A and coset B.
import sys, time, random
import numpy as np
from collections import deque

def closure(gens, d):
    e = tuple(range(d))
    els = [e]; idx = {e: 0}; q = deque([e])
    while q:
        x = q.popleft()
        for g in gens:
            y = tuple(x[g[i]] for i in range(d))   # x*g
            if y not in idx:
                idx[y] = len(els); els.append(y); q.append(y)
    return els, idx

class Grp:
    def __init__(self, gens, d):
        els, idx = closure(gens, d)
        self.N = len(els); self.d = d
        self.P = np.array(els, dtype=np.int32)
        rng = np.random.default_rng(12345)
        self.r = rng.integers(1, 2**62, size=d, dtype=np.int64).astype(np.uint64)
        H = (self.P.astype(np.uint64) * self.r).sum(axis=1, dtype=np.uint64)
        self.order = np.argsort(H); self.Hs = H[self.order]
        self.e = 0
        assert idx[tuple(range(d))] == 0
    def hidx(self, rows):
        H = (rows.astype(np.uint64) * self.r).sum(axis=1, dtype=np.uint64)
        pos = np.searchsorted(self.Hs, H)
        pos = np.minimum(pos, self.N - 1)
        ok = self.Hs[pos] == H
        assert ok.all()
        return self.order[pos]
    def mulidx(self, xs, ys):
        # xs, ys: index arrays (broadcast); returns index of x*y
        X = self.P[xs]; Y = self.P[ys]
        if X.ndim == 1: X = X[None, :]; Y = Y[None, :]
        rows = np.take_along_axis(X, Y, axis=1)
        return self.hidx(rows)
    def mul_right_all(self, a):
        # index of x*a for all x
        return self.hidx(self.P[:, self.P[a]])
    def subgroups4(self):
        allidx = np.arange(self.N)
        # involutions and order-4 elements
        sq = self.mulidx(allidx, allidx)
        sq2 = self.mulidx(sq, sq)
        invol = np.where((sq == 0) & (allidx != 0))[0]
        ord4 = np.where((sq2 == 0) & (sq != 0))[0]
        subs = set()
        for g in ord4:
            g2 = sq[g]; g3 = self.mulidx(np.array([g]), np.array([g2]))[0]
            subs.add(tuple(sorted([0, int(g), int(g2), int(g3)])))
        for a in invol:
            prods = self.mulidx(np.full(len(invol), a), invol)
            for b, ab in zip(invol, prods):
                if b <= a: continue
                if ab == 0 or ab == a or ab == b: continue
                if self.mulidx(np.array([b]), np.array([a]))[0] != ab: continue
                if sq[ab] != 0: continue
                subs.add(tuple(sorted([0, int(a), int(b), int(ab)])))
        return sorted(subs)

def graph(G, A, B):
    c1 = None; c2 = None
    for a in A:
        arr = G.mul_right_all(a)
        c1 = arr if c1 is None else np.minimum(c1, arr)
    for b in B:
        arr = G.mul_right_all(b)
        c2 = arr if c2 is None else np.minimum(c2, arr)
    u1, id1 = np.unique(c1, return_inverse=True)
    u2, id2 = np.unique(c2, return_inverse=True)
    n1 = len(u1); n2 = len(u2)
    return id1, id2, n1, n2

def evaluate(G, A, B):
    id1, id2, n1, n2 = graph(G, A, B)
    if n1 != n2: return None
    n = n1 + n2
    adj = [[] for _ in range(n)]
    for x in range(G.N):
        a = int(id1[x]); b = n1 + int(id2[x])
        adj[a].append(b); adj[b].append(a)
    if any(len(l) != 4 for l in adj): return None
    def dist_from(s):
        dist = [-1] * n; dist[s] = 0; dq = deque([s])
        while dq:
            v = dq.popleft()
            for w in adj[v]:
                if dist[w] < 0:
                    dist[w] = dist[v] + 1; dq.append(w)
        return dist
    d0 = dist_from(0); d1 = dist_from(n1)
    if min(d0) < 0 or min(d1) < 0: return dict(n=n, cost=10**9, ecc=10**9, miss=1e9, adj=adj, n1=n1)
    cost = sum(1 for d in d0 if d > 8) + sum(1 for d in d1 if d > 8)
    return dict(n=n, cost=cost, ecc=max(max(d0), max(d1)), miss=cost / (n1), adj=adj, n1=n1)

def write_edges(res, path):
    adj = res['adj']; n = res['n']
    with open(path, 'w') as f:
        f.write('%d\n' % n)
        for v in range(n):
            for w in adj[v]:
                if v < w: f.write('%d %d\n' % (v, w))

def run(name, gens, d, budget, nA, seed, outdir):
    t0 = time.time()
    G = Grp(gens, d)
    subs = G.subgroups4()
    print(name, 'order', G.N, 'n =', G.N // 2, 'order-4 subgroups', len(subs), flush=True)
    rnd = random.Random(seed)
    As = rnd.sample(subs, min(nA, len(subs)))
    best = None; cnt = 0; hist = {}
    for A in As:
        for B in subs:
            if time.time() - t0 > budget: break
            if set(A) & set(B) != {0}: continue
            r = evaluate(G, A, B)
            cnt += 1
            if r is None: continue
            hist[r['cost'] if r['cost'] < 10**9 else -1] = hist.get(r['cost'] if r['cost'] < 10**9 else -1, 0) + 1
            if best is None or r['cost'] < best[0]['cost']:
                best = (r, A, B)
    print(name, 'pairs', cnt, 'time %.1f' % (time.time() - t0), 'min cost', best[0]['cost'] if best else None,
          'ecc', best[0]['ecc'] if best else None, flush=True)
    if best:
        r = best[0]
        write_edges(r, outdir + '/' + name + '.edges')
        print('best', name, 'n', r['n'], 'cost', r['cost'], 'ecc', r['ecc'], 'miss %.4f' % r['miss'], 'A', best[1], 'B', best[2])
    return best
