"""Structure of the cost-c Haar sets of Z_m x|_r Z_k around a central involution z: for each set S={0,x,y,z_}
(independent python recomputation of (SS^-1)^4 and (S^-1 S)^4), where are the misses?
usage: structure.py TABLE HITSFILE M K Z"""
import sys, numpy as np
from collections import Counter
tab, hits, m, k, z = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
with open(tab, 'rb') as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    MT = np.fromfile(f, dtype=np.uint16, count=N*N).reshape(N, N).astype(np.int64)
inv = [int(np.where(MT[a] == 0)[0][0]) for a in range(N)]
def prod(X, Y): return {int(MT[x, y]) for x in X for y in Y}
def sides(S):
    A = {int(MT[s, inv[t]]) for s in S for t in S}; B = {int(MT[inv[s], t]) for s in S for t in S}
    return prod(prod(A, A), prod(A, A)), prod(prod(B, B), prod(B, B))
ab = lambda i: (i % m, i // m)
rows = [list(map(int, l.split())) for l in open(hits) if l.strip()]
cnt = Counter(); fib = Counter(); other_pairs = Counter(); jS = Counter()
for row in rows:
    c = row[0]; x, y, w = row[1:4]; S = [0, x, y, w]
    XA, XB = sides(S)
    mA = [g for g in range(N) if g not in XA]; mB = [g for g in range(N) if g not in XB]
    assert len(mA) + len(mB) == c, (c, len(mA), len(mB))
    zA, zB = z in mA, z in mB
    cnt[(zA, zB)] += 1
    oth = [g for g in mA if g != z] + [g for g in mB if g != z]
    for g in oth: fib[ab(g)[1]] += 1
    other_pairs[(len(mA) - zA, len(mB) - zB)] += 1
    jS[tuple(sorted(ab(s)[1] for s in S[1:]))] += 0  # placeholder
print('sets', len(rows))
print('(z missed on side A?, z missed on side B?) counts:', dict(cnt))
print('non-z misses per side (A,B) counts:', dict(other_pairs))
print('fibres j of the non-z misses (all sets):', dict(sorted(fib.items())))
print('kernel j=0 among non-z misses:', fib.get(0, 0))
