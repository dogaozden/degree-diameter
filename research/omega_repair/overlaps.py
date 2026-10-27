"""Check of OMEGA_REPAIR.md Lemma 4.1 on H(q) in Q(6,q) (q odd): for distinct points t, y, y' with t not on the line
yy' of PG(6,q):  |y^perp & y'^perp & opp(t)| >= q^3 - q^2;  for three points y, y', y'' not on one line of PG(6,q):
|y^perp & y'^perp & y''^perp & Q| <= 2q^2 + q + 1.  Here x^perp & Q = points at hexagon distance <= 4 from x.
Random samples plus structured ones (points on common totally singular lines).  usage: overlaps.py q samples"""
import sys, random, numpy as np
sys.path.insert(0, '.')
from geo import Hex
q = int(sys.argv[1]); S = int(sys.argv[2]); H = Hex(f'hex_q{q}.txt'); F = H.F; n = H.n; rng = random.Random(3)
P = H.P
def perp(x):                                    # boolean vector: points perpendicular to x (B = 0)
    A, M = F.ADD, F.MUL
    s = A[M[P[:, 0], x[4]], M[P[:, 4], x[0]]]; s = A[s, A[M[P[:, 1], x[5]], M[P[:, 5], x[1]]]]; s = A[s, A[M[P[:, 2], x[6]], M[P[:, 6], x[2]]]]
    t = M[P[:, 3], x[3]]; return A[s, F.NEG[A[t, t]]] == 0
def rank(vs):
    M = np.array(vs, dtype=np.int64) % q; r = 0; rows, cols = M.shape
    for c in range(cols):
        piv = next((i for i in range(r, rows) if M[i, c]), None)
        if piv is None: continue
        M[[r, piv]] = M[[piv, r]]; M[r] = F.MUL[F.INV[M[r, c]], M[r]]
        for i in range(rows):
            if i != r and M[i, c]: M[i] = F.ADD[M[i], F.MUL[F.NEG[M[i, c]], M[r]]]
        r += 1
    return r
PP = [perp(P[i]) for i in range(n)] if n < 5000 else None
def pp(i): return PP[i] if PP is not None else perp(P[i])
mn2, mx3 = 10 ** 9, -1
for s in range(S):
    t, y, y2, y3 = rng.sample(range(n), 4)
    if s % 3 == 1:                               # structured: y2 on a hexagon line through y
        L = H.L[rng.choice(H.lines_of[y])]; y2 = int(rng.choice([p for p in L if p != y]))
    if rank([P[t], P[y], P[y2]]) == 3:
        v = (pp(y) & pp(y2) & ~pp(t)).sum(); mn2 = min(mn2, v)
    if rank([P[y], P[y2], P[y3]]) == 3:
        v = (pp(y) & pp(y2) & pp(y3)).sum(); mx3 = max(mx3, v)
print(f"q={q}: min pair overlap in opp(t) = {mn2} (claim >= q^3-q^2 = {q**3-q*q});  max triple intersection = {mx3} (claim <= 2q^2+q+1 = {2*q*q+q+1})")
