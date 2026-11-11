"""Theorem 4.2's hypothesis on actual twists: for the starved pair (unbarred class k = 0, copy c' = 3 at position k+3 of
the first a-block; N(k,c') = the copies at position k-1 = 4 of every block), count the points t for which the six points
t, y_i = lam_{c'} lam_{c_i}^-1 (t) are distinct with no three on a line of PG(6,q).
usage: genpos.py hex_qQ.txt twists.bin"""
import sys, numpy as np, itertools
sys.path.insert(0, '.')
from geo import Hex
H = Hex(sys.argv[1]); F = H.F; n = H.n; q = H.q
raw = np.fromfile(sys.argv[2], dtype=np.int32); C = raw[0]; lam = raw[2:].reshape(C, 2, n)[:, 0, :]   # point perms
inv = np.argsort(lam, axis=1)
cp = 3; Ns = [4 + 5 * B for B in range(C // 5)]
Y = [lam[cp][inv[c]] for c in Ns]                      # y_i(t) for all t
pts = np.stack([np.arange(n)] + Y, axis=1)             # n x 6 point indices
def collinear(a, b, c):                                 # three distinct points of Q on one line of PG(6,q)
    # rank of the 3 coordinate vectors is 2  <=>  c is in span(a, b): test c = a*x + b (+ the point a itself excluded)
    A, B, Cc = H.P[a], H.P[b], H.P[c]
    for x in range(q):
        v = H.normalize(F.ADD[F.MUL[x, A], B][None, :])[0]
        if (v == Cc).all(): return True
    return False
good = 0; coinc = 0; coll = 0
for t in range(n):
    s = pts[t]
    if len(set(s.tolist())) < 6: coinc += 1; continue
    bad = False
    for a, b, c in itertools.combinations(s.tolist(), 3):
        # quick filter: collinear singular points are pairwise perpendicular
        if H.B(H.P[a], H.P[b]) or H.B(H.P[a], H.P[c]) or H.B(H.P[b], H.P[c]): continue
        if collinear(a, b, c): bad = True; break
    if bad: coll += 1
    else: good += 1
print(f"q={q}: points t in general position for the starved pair: {good} of {n}; with a coincidence: {coinc}; with a collinear triple: {coll}")
