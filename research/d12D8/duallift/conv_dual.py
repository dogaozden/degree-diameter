"""Duality phi of H(9) from research/d10D7/dual/dualfind.c (hexgen2 labelling) -> labelling of ../omega/hexq6 (same
Q(6,q) model and GF(9) encoding a+3b, i^2=-1; points matched by normalized coordinates, lines by point sets).
Checks that the result maps points to lines, lines to points and preserves every incidence.
usage: conv_dual.py HEXBIN PHI MYHEX OUT.npy     (OUT: 2n ints, delta of point p at p (a line id in [0,n)), of line l at n+l)"""
import sys, numpy as np
b = open(sys.argv[1], 'rb').read(); q, N, L = np.frombuffer(b[:12], np.int32)
LP2 = np.frombuffer(b[12:12 + 4 * L * (q + 1)], np.int32).reshape(L, q + 1)
C2 = np.frombuffer(b[12 + 4 * L * (q + 1):], np.uint8).reshape(N, 7).astype(np.int64)
phi = np.fromfile(sys.argv[2], np.int32)
f = open(sys.argv[3]); q1, n, nl = map(int, f.readline().split())
LP = np.array([list(map(int, f.readline().split())) for _ in range(nl)]); P = np.array([list(map(int, f.readline().split()[1:])) for _ in range(n)])
MUL = np.array([[((x % 3) * (y % 3) - (x // 3) * (y // 3)) % 3 + 3 * (((x % 3) * (y // 3) + (x // 3) * (y % 3)) % 3) for y in range(9)] for x in range(9)])
INV = np.array([list(MUL[x]).index(1) if x else 0 for x in range(9)])
def norm(X):
    first = (X != 0).argmax(1); s = INV[X[np.arange(len(X)), first]]; return MUL[X, s[:, None]]
pw = 9 ** np.arange(6, -1, -1)
key_mine = {k: i for i, k in enumerate((norm(P) * pw).sum(1))}
pmap = np.array([key_mine[k] for k in (norm(C2) * pw).sum(1)])          # hexgen2 point -> my point
lkey = {tuple(sorted(r)): i for i, r in enumerate(LP)}
lmap = np.array([lkey[tuple(sorted(pmap[r]))] for r in LP2])               # hexgen2 line -> my line
ipm = np.argsort(pmap); ilm = np.argsort(lmap)
d = np.empty(2 * n, np.int64)
for p in range(n):  # my point p = hexgen2 point ipm[p]; phi of it = hexgen2 line phi[ipm[p]] - N
    x = phi[ipm[p]]; assert x >= N; d[p] = lmap[x - N]
for l in range(n):
    x = phi[N + ilm[l]]; assert x < N; d[n + l] = pmap[x]
assert len(set(d[:n])) == n and len(set(d[n:])) == n
# incidence check: p on l  =>  d[l] (a point) on line d[p]
for l in range(n):
    for p in LP[l]: assert d[n + l] in set(LP[d[p]].tolist())
np.save(sys.argv[4], d); print("duality ok: points->lines, lines->points, all", n * (q + 1), "incidences preserved")
