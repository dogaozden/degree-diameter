"""Automorphisms of the split Cayley hexagon H(q) built by hexq6 (Q(6,q) model), from SL(3,q) <= G_2(q) acting as
x = (u | x3 | w) -> (A u | x3 | A^-T w), plus the Frobenius map for q = 9. Each map is checked to send every H-line to an
H-line before it is saved. Output: an .npy array of shape (g, 2n): permutations of the incidence-graph vertices
(points 0..n-1, lines n..2n-1).   usage: haut.py hex.txt out.npy [singer] [trans] [frob]"""
import sys, itertools, numpy as np
f = open(sys.argv[1]); q, n, nl = map(int, f.readline().split())
L = np.array([list(map(int, f.readline().split())) for _ in range(nl)], dtype=np.int64)
P = np.array([list(map(int, f.readline().split()[1:])) for _ in range(n)], dtype=np.int64)
if q == 9:
    ADD = np.array([[(x % 3 + y % 3) % 3 + 3 * ((x // 3 + y // 3) % 3) for y in range(9)] for x in range(9)])
    MUL = np.array([[((x % 3) * (y % 3) - (x // 3) * (y // 3)) % 3 + 3 * (((x % 3) * (y // 3) + (x // 3) * (y % 3)) % 3) for y in range(9)] for x in range(9)])
else:
    ADD = np.array([[(x + y) % q for y in range(q)] for x in range(q)]); MUL = np.array([[x * y % q for y in range(q)] for x in range(q)])
NEG = np.array([list(ADD[x]).index(0) for x in range(q)]); INV = np.array([list(MUL[x]).index(1) if x else 0 for x in range(q)])
def madd(a, b): return ADD[a, b]
def mat_mul(A, B):
    m, k = A.shape; k2, nn = B.shape; C = np.zeros((m, nn), dtype=np.int64)
    for i in range(k): C = ADD[C, MUL[A[:, i:i + 1], B[i:i + 1, :]]]
    return C
def mat_inv(A):
    m = A.shape[0]; M = np.concatenate([A.copy(), np.eye(m, dtype=np.int64)], axis=1)
    for c in range(m):
        r = next(r for r in range(c, m) if M[r, c]); M[[c, r]] = M[[r, c]]; M[c] = MUL[INV[M[c, c]], M[c]]
        for r in range(m):
            if r != c and M[r, c]: M[r] = ADD[M[r], MUL[NEG[M[r, c]], M[c]]]
    return M[:, m:]
code_of = {}
pw = q ** np.arange(6, -1, -1)
lut = -np.ones(q ** 7, dtype=np.int64); lut[(P * pw).sum(1)] = np.arange(n)
def normalize(X):
    X = X.copy(); first = (X != 0).argmax(1); s = INV[X[np.arange(len(X)), first]]; return MUL[X, s[:, None]]
def point_perm(M):
    Y = normalize(mat_mul(P, M.T)); idx = lut[(Y * pw).sum(1)]; assert (idx >= 0).all(); return idx
Lkey = {tuple(r[:2]): i for i, r in enumerate(np.sort(L, 1))}
def full_perm(pp):
    img = np.sort(pp[L], 1); lp = np.array([Lkey.get(tuple(r[:2]), -1) for r in img])
    assert (lp >= 0).all(), "a line is not mapped to a line"
    assert (np.sort(L[lp], 1) == img).all(), "a line is not mapped to a line"
    assert len(set(pp.tolist())) == n and len(set(lp.tolist())) == nl
    return np.concatenate([pp, n + lp])
def embed(A):
    M = np.zeros((7, 7), dtype=np.int64); M[:3, :3] = A; M[3, 3] = 1; M[4:, 4:] = mat_inv(A).T; return M
def order(A):
    I = np.eye(3, dtype=np.int64); B = A.copy(); k = 1
    while not (B == I).all(): B = mat_mul(B, A); k += 1
    return k
gens = []
want = sys.argv[3:] or ['singer', 'trans']
if 'singer' in want:
    target = q * q + q + 1
    for a, b in itertools.product(range(q), repeat=2):
        A = np.array([[0, 0, 1], [1, 0, NEG[b]], [0, 1, NEG[a]]], dtype=np.int64)  # companion of x^3 + a x^2 + b x - 1
        if order(A) == target: break
    print("singer: order", order(A), "det-free companion a,b =", a, b); gens.append(full_perm(point_perm(embed(A))))
if 'trans' in want:
    A = np.eye(3, dtype=np.int64); A[0, 1] = 1; print("transvection order", order(A)); gens.append(full_perm(point_perm(embed(A))))
if 'frob' in want and q == 9:
    FR = np.array([x % 3 + 3 * ((-(x // 3)) % 3) for x in range(9)]); Y = FR[P]; Y = normalize(Y); pp = lut[(Y * pw).sum(1)]
    gens.append(full_perm(pp)); print("frobenius")
G = np.array(gens); np.save(sys.argv[2], G); print("saved", G.shape)
