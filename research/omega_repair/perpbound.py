"""OMEGA_REPAIR.md Lemma 4.4 at q = 7, sampled: for random h in G_2(7) without fixed points on the points of H(7),
d_c = dim ker(h + h^-1 - c) (c in F_q), the bound (q^5-1)/(q-1) + sum_c q^(1.5 + d_c/2), and the true |Perp(h)|.
usage: perpbound.py samples seed"""
import sys, random, numpy as np
sys.path.insert(0, '.')
from geo import Hex
from mktwist import rand_elem
S = int(sys.argv[1]); rng = random.Random(int(sys.argv[2]))
H = Hex('hex_q7.txt'); F = H.F; n = H.n; P = H.P; q = 7; A, M = F.ADD, F.MUL
def Bvec(X, Y):
    s = A[M[X[:, 0], Y[:, 4]], M[X[:, 4], Y[:, 0]]]; s = A[s, A[M[X[:, 1], Y[:, 5]], M[X[:, 5], Y[:, 1]]]]
    s = A[s, A[M[X[:, 2], Y[:, 6]], M[X[:, 6], Y[:, 2]]]]; t = M[X[:, 3], Y[:, 3]]; return A[s, F.NEG[A[t, t]]]
def rank(Mx):
    Mx = Mx.copy() % q; r = 0
    for c in range(Mx.shape[1]):
        piv = next((i for i in range(r, Mx.shape[0]) if Mx[i, c]), None)
        if piv is None: continue
        Mx[[r, piv]] = Mx[[piv, r]]; Mx[r] = M[F.INV[Mx[r, c]], Mx[r]]
        for i in range(Mx.shape[0]):
            if i != r and Mx[i, c]: Mx[i] = A[Mx[i], M[F.NEG[Mx[i, c]], Mx[r]]]
        r += 1
    return r
cnt = 0; maxd = 0; maxsum = 0; worst_gap = 10 ** 9
for s in range(S):
    h = rand_elem(H, rng, 12)
    Y = H.normalize(F.mm(P, h.T)); pp = H.lut[(Y * H.pwv).sum(1)]
    if (pp == np.arange(n)).any(): continue
    cnt += 1
    S_ = A[h, F.inv(h)]
    d = [7 - rank(A[S_, M[F.NEG[c], np.eye(7, dtype=np.int64)]]) for c in range(q)]
    bound = (q ** 5 - 1) / (q - 1) + sum(q ** (1.5 + x / 2) for x in d)
    perp = int((Bvec(P, P[pp]) == 0).sum())
    maxd = max(maxd, max(d)); maxsum = max(maxsum, sum(d)); worst_gap = min(worst_gap, bound - perp)
print(f"q=7: {cnt} fixed-point-free elements sampled; max d_c = {maxd} (claim <= 4); max sum d_c = {maxsum} (<= 7); "
      f"min (bound - |Perp|) = {worst_gap:.1f} (>= 0); universal bound (q^5-1)/(q-1) + q^3.5 + q^3 + (q-2) q^1.5 = "
      f"{(q**5-1)/(q-1) + q**3.5 + q**3 + (q-2)*q**1.5:.1f}")
