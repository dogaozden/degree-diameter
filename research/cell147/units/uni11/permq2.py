# Permutation of the points of E_q = {x4 = -C x0} (prime q) induced by the similitude g = (R^k T0 on A) (+) (P on V4):
# V4 = (x1,x2,x5,x6) ~ X = [[x1, x2], [-x6, x5]] with Q4 = det X; P = left (L) or right (R) multiplication by
# [[0,1],[nu,0]] (P^2 = nu, multiplier -nu; nu = -1 if q = 3 mod 4, else the least non-square); T0 = a similitude of
# A = (x0,x3) (Q_A = -C x0^2 - x3^2) with multiplier -nu, R = generator of SO(A). Similitudes preserve E and
# orthogonality, so they act on partial ovoids. Usage: python3 permq2.py q C L|R t OUT (t indexes the similitudes T of A)
import sys
import numpy as np
q, C, mode, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
sq = {x * x % q for x in range(1, q)}
nu = q - 1 if q % 4 == 3 else min(x for x in range(2, q) if x not in sq)
mult = (-nu) % q
def QA(x0, x3): return (-C * x0 * x0 - x3 * x3) % q
def sim(m):
    for a in range(q):
        for b in range(q):
            for c in range(q):
                for d in range(q):
                    if (a * d - b * c) % q == 0: continue
                    if all(QA(a * u + b * v, c * u + d * v) == m * QA(u, v) % q for u, v in ((1, 0), (0, 1), (1, 1))):
                        yield np.array([[a, b], [c, d]], dtype=np.int64)
SIMS = list(sim(mult))
T0 = SIMS[0]
R = None
for M_ in sim(1):
    if (M_[0, 0] * M_[1, 1] - M_[0, 1] * M_[1, 0]) % q != 1: continue
    P_ = np.eye(2, dtype=np.int64); o = 0
    while True:
        P_ = (P_ @ M_) % q; o += 1
        if np.array_equal(P_, np.eye(2, dtype=np.int64)): break
    if o == q + 1: R = M_; break
G = SIMS[k % len(SIMS)]   # k indexes all similitudes of A with multiplier -nu
Y = X.copy()
Y[:, 0] = (G[0, 0] * X[:, 0] + G[0, 1] * X[:, 3]) % q
Y[:, 3] = (G[1, 0] * X[:, 0] + G[1, 1] * X[:, 3]) % q
Y[:, 4] = (-C * Y[:, 0]) % q
x1, x2, x5, x6 = X[:, 1], X[:, 2], X[:, 5], X[:, 6]
if mode == 'L': Y[:, 1], Y[:, 2], Y[:, 5], Y[:, 6] = -x6, x5, nu * x2, -nu * x1
else: Y[:, 1], Y[:, 2], Y[:, 5], Y[:, 6] = nu * x2, x1, -x6, -nu * x5
Y %= q
assert np.all((Y[:, 0] * Y[:, 4] + Y[:, 1] * Y[:, 5] + Y[:, 2] * Y[:, 6] - Y[:, 3] ** 2) % q == 0)
def norm(A):
    first = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), first]
    return (A * np.array(INV)[lead][:, None]) % q
PW = q ** np.arange(7)
key = {int(v): i for i, v in enumerate(norm(X) @ PW)}
perm = np.array([key[int(v)] for v in norm(Y) @ PW])
np.savetxt(out, perm, fmt='%d')
print(f"q={q} nu={nu} T={G.tolist()} (of {len(SIMS)}) mode={mode}")
