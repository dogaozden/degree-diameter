import sys, numpy as np
from collections import Counter
f = open(sys.argv[1]).read().split()
n, dg = int(f[0]), int(f[1]); V = 2*n
ln = np.array(f[2:2+n*dg], dtype=int).reshape(n, dg); sig = np.array(f[2+n*dg:2+n*dg+n], dtype=int)
B = np.zeros((V, V), dtype=np.int64)
for l in range(n):
    for p in ln[l]: B[p, n+l] += 1; B[n+l, p] += 1
P = [np.eye(V, dtype=np.int64)]
for k in range(1, 7): P.append(P[-1] @ B)
dist = np.full((V, V), 99)
for k in range(6, -1, -1): dist[P[k] > 0] = k
PL = dist[:n, n:]   # point-line distances
missL = (PL >= 5).sum(axis=0)   # per line, points at >=5
missP = (PL >= 5).sum(axis=1)
print("point-line pairs at >=5:", int((PL >= 5).sum()), " lines with miss counts:", Counter(missL.tolist()))
print("points with miss counts:", Counter(missP.tolist()))
for side, sl in (("PP", slice(0, n)), ("LL", slice(n, V))):
    D = dist[sl, sl]; c4 = P[4][sl, sl]
    far = (D >= 6).sum()
    sg = ((D == 4) & (c4 == 1)).sum()
    print(side, "pairs dist>=6 (ordered):", int(far), " dist4 single-geodesic:", int(sg))
big = [(int(missL[l]), l) for l in range(n) if missL[l] > n-585]
big.sort(reverse=True); print("lines with extra misses:", big[:30])
bigp = [(int(missP[p]), p) for p in range(n) if missP[p] > n-585]; bigp.sort(reverse=True); print("points with extra misses:", bigp[:30])
