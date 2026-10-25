#!/usr/bin/env python3
"""fill.py QUOT NINESOL: fix the quotient vertices in NINESOL (weight-9 ids, one per line), then the exact maximum weight
of an independent set among the light (weight 1/3) quotient vertices not adjacent to them. Prints total weight."""
import sys
W = []; adj = []
with open(sys.argv[1]) as f:
    n = int(f.readline())
    for i in range(n):
        a = list(map(int, f.readline().split()))
        W.append(a[0]); adj.append(set(a[2:2 + a[1]]))
A = [int(l) for l in open(sys.argv[2]) if l.strip()]
Aset = set(A)
assert all(not (adj[v] & Aset) for v in A), 'fixed set not independent'
base = sum(W[v] for v in A)
resid = [v for v in range(n) if W[v] < 9 and not (adj[v] & Aset) and v not in Aset]
idx = {v: i for i, v in enumerate(resid)}
m = len(resid)
nbm = [0] * m
for v in resid:
    for u in adj[v]:
        if u in idx: nbm[idx[v]] |= 1 << idx[u]
wt = [W[v] for v in resid]
best = [0, 0]
sys.setrecursionlimit(10000)
def bb(cand, cur):
    # cand: bitmask of candidates; cur: weight so far
    if cur + sum(wt[i] for i in range(m) if cand >> i & 1) <= best[0]:
        return
    if cand == 0:
        if cur > best[0]: best[0] = cur; best[1] = 1
        return
    i = (cand & -cand).bit_length() - 1
    bb(cand & ~nbm[i] & ~(1 << i), cur + wt[i])   # take i
    bb(cand & ~(1 << i), cur)                      # skip i
bb((1 << m) - 1, 0)
print('nines', len(A), 'base', base, 'residual_light', m, 'best_fill', best[0], 'total', base + best[0])
