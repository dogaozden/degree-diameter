"""Analyse all cost-2 Haar sets S={0,x,y,z} of Z_101 x|_5 Z_25 (hx hit file).  Element idx = a + 101 j -> (a, j).
Independent recomputation of (SS^-1)^4 and (S^-1 S)^4 with python sets (not hx's code)."""
import sys, numpy as np
from collections import Counter, defaultdict
m, k = 101, 25
with open('g101.tab', 'rb') as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    MT = np.fromfile(f, dtype=np.uint16, count=N*N).reshape(N, N).astype(np.int64)
inv = [int(np.where(MT[a] == 0)[0][0]) for a in range(N)]
def prod(X, Y):
    return {int(MT[x, y]) for x in X for y in Y}
def sides(S):
    A = {int(MT[s, inv[t]]) for s in S for t in S}
    B = {int(MT[inv[s], t]) for s in S for t in S}
    XA = prod(prod(A, A), prod(A, A)); XB = prod(prod(B, B), prod(B, B))
    return XA, XB
def ab(i): return (i % m, i // m)
rows = [list(map(int, l.split())) for l in open('hits101_L2.txt') if l.strip()]
miss_by_side = {'A': Counter(), 'B': Counter()}   # fibre j of missed elements
kernel_hits = Counter()   # sets where a missed element has j=0
jpatterns = Counter()
detail = []
allmiss = []
for c, x, y, z in rows:
    S = [0, x, y, z]
    XA, XB = sides(S)
    mA = [g for g in range(N) if g not in XA]
    mB = [g for g in range(N) if g not in XB]
    assert len(mA) + len(mB) == 2, (x, y, z, len(mA), len(mB))
    jS = tuple(sorted(ab(s)[1] for s in S[1:]))
    jpatterns[jS] += 1
    for side, lst in (('A', mA), ('B', mB)):
        for g in lst:
            a, j = ab(g)
            miss_by_side[side][j] += 1
    kern = any(ab(g)[1] == 0 for g in mA + mB)
    kernel_hits[kern] += 1
    detail.append((x, y, z, [ab(g) for g in mA], [ab(g) for g in mB], [ab(s) for s in S[1:]]))
    allmiss.append((mA, mB))
print('sets', len(rows), 'all cost 2 verified:', all(len(a)+len(b) == 2 for a, b in allmiss))
print('split of cost: (A,B) =', Counter((len(a), len(b)) for a, b in allmiss))
print('missed-element fibres j (count over all missed points), side A:', dict(sorted(miss_by_side['A'].items())))
print('missed-element fibres j, side B:', dict(sorted(miss_by_side['B'].items())))
print('sets with a missed element in kernel j=0:', dict(kernel_hits))
print('j-multisets of S\\{0}:', dict(jpatterns))
print('distinct missed (a,j) pairs:', sorted(set(ab(g) for a, b in allmiss for g in a+b)))
for d in detail:
    print('S=(0,%s)' % ','.join('(%d,%d)' % p for p in d[5]), 'missA', d[3], 'missB', d[4])
