"""Check that the missed sets of (SS^-1)^4 and (S^-1 S)^4 are closed under g -> g^-1 (they are, since X = SS^-1 is inverse-closed).
Also checks the two misses of cost-2 101 sets are inverse pairs. usage: invcheck.py TABLE HITSFILE"""
import sys, numpy as np
from collections import Counter
tab, hits = sys.argv[1], sys.argv[2]
with open(tab, 'rb') as f:
    N = int(np.fromfile(f, dtype=np.int32, count=1)[0])
    MT = np.fromfile(f, dtype=np.uint16, count=N*N).reshape(N, N).astype(np.int64)
inv = [int(np.where(MT[a] == 0)[0][0]) for a in range(N)]
def prod(X, Y): return {int(MT[x, y]) for x in X for y in Y}
def sides(S):
    A = {int(MT[s, inv[t]]) for s in S for t in S}; B = {int(MT[inv[s], t]) for s in S for t in S}
    return prod(prod(A, A), prod(A, A)), prod(prod(B, B), prod(B, B))
rows = [list(map(int, l.split())) for l in open(hits) if l.strip()]
closed = Counter(); pairs = Counter()
for row in rows:
    x, y, w = row[1:4]; S = [0, x, y, w]
    XA, XB = sides(S)
    for M in ([g for g in range(N) if g not in XA], [g for g in range(N) if g not in XB]):
        Ms = set(M)
        closed[all(inv[g] in Ms for g in M)] += 1
        if M and len(M) == 2 and M[0] != M[1]: pairs[inv[M[0]] == M[1]] += 1
print('sets', len(rows), 'missed sets inverse-closed (per side):', dict(closed), ' 2-element side-misses are inverse pairs:', dict(pairs))
