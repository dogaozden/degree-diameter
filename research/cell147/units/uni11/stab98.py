# Stabilizer of a q=7 partial ovoid S in PGO(V), V = {x4 = -C x0}, through its centers Z (poles of the q^2-point
# tangent hyperplanes). Candidates: g maps 5 independent centers to centers (with scalars fixed by B), and the pole n0 of
# H0 = <Z> to +-mu n0. Usage: python3 stab98.py FLAGS q C
import sys, itertools
import numpy as np
fl, q, C = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
rows = np.loadtxt(f'/home/user/degree-diameter/research/cell147/data/E{q}.map', dtype=np.int64)
pos = {int(r[0]): i for i, r in enumerate(rows)}
S = [pos[int(l.split()[0])] for l in open(fl)]
ALL = rows[:, 2:9] % q
U = ALL[:, [0, 1, 2, 3, 5, 6]]
M = np.zeros((6, 6), dtype=np.int64)
M[0, 0] = (-2 * C) % q; M[1, 4] = M[4, 1] = 1; M[2, 5] = M[5, 2] = 1; M[3, 3] = (-2) % q
INV = [0] + [pow(a, q - 2, q) for a in range(1, q)]
SQRT = {}
for x in range(1, q): SQRT.setdefault(x * x % q, x)
def solve(A, B_):     # A X = B_ mod q, A square invertible
    n = A.shape[0]; T = np.concatenate([A % q, B_ % q], axis=1)
    for c in range(n):
        piv = next(i for i in range(c, n) if T[i, c]); T[[c, piv]] = T[[piv, c]]; T[c] = (T[c] * INV[T[c, c]]) % q
        for i in range(n):
            if i != c and T[i, c]: T[i] = (T[i] - T[i, c] * T[c]) % q
    return T[:, n:]
def norm(A):
    first = np.argmax(A != 0, axis=1); lead = A[np.arange(len(A)), first]
    return (A * np.array(INV)[lead][:, None]) % q
PW = q ** np.arange(6)
key = {int(v): i for i, v in enumerate(norm(U) @ PW)}
Sset = set(S)
# centers: poles of hyperplanes containing q^2 points of S
allv = np.array(list(itertools.product(range(q), repeat=6)), dtype=np.int64)
nz = allv[np.any(allv != 0, axis=1)]; first = np.argmax(nz != 0, axis=1); nrm = nz[nz[np.arange(len(nz)), first] == 1]
US = U[S]
cnt = ((nrm @ US.T) % q == 0).sum(axis=1)
H = nrm[cnt == q * q]
Mi = solve(M, np.eye(6, dtype=np.int64))
Z = norm((H @ Mi.T) % q)
nZ = len(Z); print(nZ, "centers")
# basis: 5 independent centers; n0 = pole of their span
def rank(A):
    A = A.copy() % q; r = 0
    for c in range(A.shape[1]):
        piv = next((i for i in range(r, A.shape[0]) if A[i, c]), None)
        if piv is None: continue
        A[[r, piv]] = A[[piv, r]]; A[r] = (A[r] * INV[A[r, c]]) % q
        for i in range(A.shape[0]):
            if i != r and A[i, c]: A[i] = (A[i] - A[i, c] * A[r]) % q
        r += 1
    return r
base = []
for i in range(nZ):
    if rank(np.array(base + [Z[i]])) > len(base): base.append(Z[i])
    if len(base) == 5: break
base = np.array(base); bidx = [next(j for j in range(nZ) if np.array_equal(Z[j], b)) for b in base]
# n0: B(n0, base_i) = 0
for v in allv[1:]:
    if not np.any((base @ M @ v) % q): n0 = v; break
Qn0 = int(n0 @ M @ n0) % q
print("n0", n0.tolist(), "B(n0,n0) =", Qn0)
Gb = (base @ M @ base.T) % q
found = []
for img in itertools.permutations(range(nZ), 5):
    T = Z[list(img)]
    Gt = (T @ M @ T.T) % q
    # lambda_i lambda_j Gt_ij = Gb_ij
    if any((Gt[i, j] == 0) != (Gb[i, j] == 0) for i in range(5) for j in range(5)): continue
    r01 = Gb[0, 1] * INV[Gt[0, 1]] % q; r02 = Gb[0, 2] * INV[Gt[0, 2]] % q; r12 = Gb[1, 2] * INV[Gt[1, 2]] % q
    l0sq = r01 * r02 % q * INV[r12] % q
    if l0sq not in SQRT: continue
    for s0 in (1, -1):
        l0 = s0 * SQRT[l0sq] % q
        lam = [l0] + [Gb[0, j] * INV[Gt[0, j]] % q * INV[l0] % q for j in range(1, 5)]
        if any(lam[i] * lam[j] % q * Gt[i, j] % q != Gb[i, j] for i in range(5) for j in range(5)): continue
        for mu in range(1, q):
            if mu * mu % q != 1: continue
            src = np.vstack([base, n0]); dst = np.vstack([(T * np.array(lam)[:, None]) % q, (mu * n0) % q])
            g = solve(src, dst).T % q        # g src_i = dst_i  ->  src g^T = dst
            if not np.array_equal((g.T @ M @ g) % q, M): continue
            img_all = norm((U @ g.T) % q) @ PW
            imgS = {key[int(v)] for v in img_all[S]}
            if imgS == Sset: found.append(g)
print("stabilizer elements found (projective):", len(found))
np.save('stab98.npy', np.array(found))
