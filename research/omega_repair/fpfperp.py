"""For random elements h of G_2(q) (random words in SL(3,q) and long root elations), the number of fixed points on the
points of H(q) and |Perp(h)| = #{s : h(s) perpendicular to s (hexagon distance <= 4)}, as a fraction of N.
usage: fpfperp.py q samples seed [wordlen]"""
import sys, random, numpy as np
sys.path.insert(0, '.')
from geo import Hex
from mktwist import rand_elem
q = int(sys.argv[1]); S = int(sys.argv[2]); rng = random.Random(int(sys.argv[3])); wl = int(sys.argv[4]) if len(sys.argv) > 4 else 12
H = Hex(f'hex_q{q}.txt'); F = H.F; n = H.n; P = H.P
A, M = F.ADD, F.MUL
def Bvec(X, Y):
    s = A[M[X[:, 0], Y[:, 4]], M[X[:, 4], Y[:, 0]]]; s = A[s, A[M[X[:, 1], Y[:, 5]], M[X[:, 5], Y[:, 1]]]]
    s = A[s, A[M[X[:, 2], Y[:, 6]], M[X[:, 6], Y[:, 2]]]]; t = M[X[:, 3], Y[:, 3]]; return A[s, F.NEG[A[t, t]]]
def order(pp):
    k, cur = 1, pp.copy()
    while not (cur == np.arange(n)).all():
        cur = pp[cur]; k += 1
        if k > 10 ** 6: return -1
    return k
stats = []
for i in range(S):
    G = rand_elem(H, rng, wl)
    Y = H.normalize(F.mm(P, G.T)); pp = H.lut[(Y * H.pwv).sum(1)]
    fix = int((pp == np.arange(n)).sum()); perp = int((Bvec(P, P[pp]) == 0).sum())
    stats.append((fix, perp, order(pp)))
fpf = [s for s in stats if s[0] == 0]
print(f"q={q}: {S} random elements, {len(fpf)} fixed-point-free on points; max |Perp|/N over fpf = {max(s[1] for s in fpf) / n:.4f}, "
      f"over all non-identity = {max(s[1] for s in stats if s[1] < n) / n:.4f}")
from collections import Counter
print("fpf orders:", sorted(Counter(s[2] for s in fpf).items()))
print("fpf (order, |Perp|) pairs:", sorted(Counter((s[2], s[1]) for s in fpf).items())[:40])
