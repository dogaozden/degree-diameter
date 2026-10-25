# Permutation of E_q (prime q, data/E{q}.map) induced by the isometry g = R^a (+) Y^m: R a generator of SO(A) on
# A = (x0,x3) (Q_A = -C x0^2 - x3^2, order q+1), Y an elliptic element of SL(2,q) of order q+1 acting on V4 = (x1,x2,x5,x6)
# ~ X = [[x1, x2], [-x6, x5]] by right (R) or left (L) multiplication. Usage: python3 permq3.py q C a m R|L OUT
import sys
import numpy as np
q, C, a, m, side, out = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5], sys.argv[6]
I2 = np.eye(2, dtype=np.int64)
def order(M_):
    P = I2.copy()
    for o in range(1, 4 * q * q):
        P = (P @ M_) % q
        if np.array_equal(P, I2): return o
    return -1
def mpow(M_, k):
    P = I2.copy()
    for _ in range(k % (q + 1) if order(M_) == q + 1 else k): P = (P @ M_) % q
    return P
def QA(x0, x3): return (-C * x0 * x0 - x3 * x3) % q
R = None
for u in range(q):
    for v in range(q):
        for w in range(q):
            for z in range(q):
                M_ = np.array([[u, v], [w, z]], dtype=np.int64)
                if (u * z - v * w) % q != 1: continue
                if any(QA(u * s + v * t, w * s + z * t) != QA(s, t) for s, t in ((1, 0), (0, 1), (1, 1))): continue
                if order(M_) == q + 1: R = M_; break
            if R is not None: break
        if R is not None: break
    if R is not None: break
Y = None
for t in range(q):
    if (t * t - 4) % q and pow((t * t - 4) % q, (q - 1) // 2, q) == q - 1:   # elliptic trace
        M_ = np.array([[0, -1], [1, t]], dtype=np.int64) % q
        if order(M_) == q + 1: Y = M_; break
Ra, Ym = mpow(R, a), mpow(Y, m)
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
X = rows[:, 2:9] % q
INV = [0] + [pow(b, q - 2, q) for b in range(1, q)]
Z = X.copy()
Z[:, 0] = (Ra[0, 0] * X[:, 0] + Ra[0, 1] * X[:, 3]) % q
Z[:, 3] = (Ra[1, 0] * X[:, 0] + Ra[1, 1] * X[:, 3]) % q
Z[:, 4] = (-C * Z[:, 0]) % q
x1, x2, x5, x6 = X[:, 1], X[:, 2], X[:, 5], X[:, 6]
k11, k12, k21, k22 = Ym[0, 0], Ym[0, 1], Ym[1, 0], Ym[1, 1]
if side == 'R':
    Z[:, 1] = x1 * k11 + x2 * k21; Z[:, 2] = x1 * k12 + x2 * k22
    Z[:, 6] = x6 * k11 - x5 * k21; Z[:, 5] = -x6 * k12 + x5 * k22
else:
    Z[:, 1] = k11 * x1 - k12 * x6; Z[:, 2] = k11 * x2 + k12 * x5
    Z[:, 6] = -(k21 * x1 - k22 * x6); Z[:, 5] = k21 * x2 + k22 * x5
Z %= q
def norm(A):
    first = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), first]
    return (A * np.array(INV)[lead][:, None]) % q
PW = q ** np.arange(7)
key = {int(v): i for i, v in enumerate(norm(X) @ PW)}
perm = np.array([key[int(v)] for v in norm(Z) @ PW])
np.savetxt(out, perm, fmt='%d')
