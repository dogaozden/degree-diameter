# Permutation of the points of E_q = {x4 = -C x0} (prime q, from data/E{q}.map) induced by g = R^k (+) J, where R is a
# generator of the rotation group SO(A) of the anisotropic plane A = (x0, x3) (Q_A = -C x0^2 - x3^2) and J acts on the
# hyperbolic 4-space (x1, x2, x5, x6) (Q4 = x1 x5 + x2 x6): J1 = left multiplication by [[0,1],[-1,0]] on
# X = [[x1, x2], [-x6, x5]], J2 = right multiplication, I = identity. Usage: python3 permq.py q C J1|J2|I k OUT
import sys
import numpy as np
q, C, mode, k, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), sys.argv[5]
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q
assert np.all(X[:, 4] == (-C * X[:, 0]) % q)
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
def QA(x0, x3): return (-C * x0 * x0 - x3 * x3) % q
# rotation generator: 2x2 matrices preserving Q_A with det 1, of order q + 1
R = None
for a in range(q):
    for b in range(q):
        for c in range(q):
            for d in range(q):
                if (a * d - b * c) % q != 1: continue
                if any(QA(a * u + b * v, c * u + d * v) != QA(u, v) for u, v in ((1, 0), (0, 1), (1, 1))): continue
                M = np.array([[a, b], [c, d]]); P = np.eye(2, dtype=np.int64); o = 0
                while True:
                    P = (P @ M) % q; o += 1
                    if np.array_equal(P, np.eye(2, dtype=np.int64)): break
                if o == q + 1: R = M; break
            if R is not None: break
        if R is not None: break
    if R is not None: break
Rk = np.eye(2, dtype=np.int64)
for _ in range(k): Rk = (Rk @ R) % q
Y = X.copy()
Y[:, 0] = (Rk[0, 0] * X[:, 0] + Rk[0, 1] * X[:, 3]) % q
Y[:, 3] = (Rk[1, 0] * X[:, 0] + Rk[1, 1] * X[:, 3]) % q
Y[:, 4] = (-C * Y[:, 0]) % q
x1, x2, x5, x6 = X[:, 1], X[:, 2], X[:, 5], X[:, 6]
if mode == 'J1': Y[:, 1], Y[:, 2], Y[:, 5], Y[:, 6] = -x6, x5, -x2, x1
elif mode == 'J2': Y[:, 1], Y[:, 2], Y[:, 5], Y[:, 6] = -x2, x1, -x6, x5
Y %= q
def norm(A):
    first = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), first]
    return (A * np.array(INV)[lead][:, None]) % q
PW = q ** np.arange(7)
key = {int(v): i for i, v in enumerate(norm(X) @ PW)}
perm = np.array([key[int(v)] for v in norm(Y) @ PW])
np.savetxt(out, perm, fmt='%d')
