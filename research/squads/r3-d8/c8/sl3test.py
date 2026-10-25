# Test whether block matrices diag(A on (0,1,2), A^{-T} on (4,5,6), 1 on 3) are automorphisms of H(q) in hexq coordinates.
import sys, itertools, random
sys.path.insert(0, '/home/user/degree-diameter/research/theorems/d8')
import numpy as np
import gh
q = int(sys.argv[1]) if len(sys.argv) > 1 else 4
H = gh.load(q)
N = H.N
F = H.F
ADD, MUL, NEG, INV = F.ADD, F.MUL, F.NEG, F.INV
P = np.array(H.P, dtype=np.int64)
POW = q ** np.arange(7, dtype=np.int64)
def normalize(V):
    V = np.array(V, dtype=np.int64)
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    return MUL[V, INV[lead][:, None]]
codes = normalize(P) @ POW
idx = {int(c): i for i, c in enumerate(codes)}
lineset = {frozenset(int(p) for p in H.lines[k]): k for k in range(N)}
def matvec_rows(M, X):
    # X: rows are vectors; returns rows M x (over GF(q))
    out = np.zeros_like(X)
    for r in range(7):
        acc = np.zeros(X.shape[0], dtype=np.int64)
        for c in range(7):
            if M[r, c]:
                acc = ADD[acc, MUL[M[r, c], X[:, c]]]
        out[:, r] = acc
    return out
def mat_mul(A, B):
    n = A.shape[0]
    C = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            acc = 0
            for k in range(n):
                acc = ADD[acc, MUL[A[i, k], B[k, j]]]
            C[i, j] = acc
    return C
def det3(A):
    a = A
    t1 = MUL[a[0,0], ADD[MUL[a[1,1],a[2,2]], NEG[MUL[a[1,2],a[2,1]]]]]
    t2 = MUL[a[0,1], ADD[MUL[a[1,0],a[2,2]], NEG[MUL[a[1,2],a[2,0]]]]]
    t3 = MUL[a[0,2], ADD[MUL[a[1,0],a[2,1]], NEG[MUL[a[1,1],a[2,0]]]]]
    return ADD[ADD[t1, NEG[t2]], t3]
def transpose_inv3(A):
    # inverse via adjugate / det
    a = A
    d = det3(a); di = INV[d]
    adj = np.zeros((3,3), dtype=np.int64)
    for i in range(3):
        for j in range(3):
            rows = [r for r in range(3) if r != j]; cols = [c for c in range(3) if c != i]
            m = ADD[MUL[a[rows[0],cols[0]], a[rows[1],cols[1]]], NEG[MUL[a[rows[0],cols[1]], a[rows[1],cols[0]]]]]
            if (i + j) % 2: m = NEG[m]
            adj[i, j] = m
    inv = MUL[adj, di]
    return inv.T  # (A^{-1})^T
def block(A):
    G = np.zeros((7, 7), dtype=np.int64)
    AiT = transpose_inv3(A)
    for r in range(3):
        for c in range(3):
            G[r, c] = A[r, c]
            G[4 + r, 4 + c] = AiT[r, c]
    G[3, 3] = 1
    return G
def perm_of(G):
    Y = matvec_rows(G, P)
    Yn = normalize(Y) @ POW
    return np.array([idx[int(c)] for c in Yn])
def is_aut(perm):
    ok = 0
    for k in range(N):
        s = frozenset(int(perm[int(p)]) for p in H.lines[k])
        if s in lineset: ok += 1
    return ok
rng = random.Random(1)
tests = 0; found = []
for trial in range(400):
    A = np.array([[rng.randrange(q) for _ in range(3)] for _ in range(3)], dtype=np.int64)
    if det3(A) != 1: continue
    tests += 1
    G = block(A)
    perm = perm_of(G)
    ok = is_aut(perm)
    if tests <= 5 or ok == N:
        print('trial', trial, 'lines preserved', ok, 'of', N, flush=True)
    if ok == N:
        found.append(A)
        if len(found) >= 3: break
print('tested SL3 elements', tests, 'automorphic found', len(found))
np.save('/home/user/degree-diameter/research/squads/r3-d8/c8/found_A_q%d.npy' % q, np.array(found)) if found else None
