"""GF(2)-subgeometry W(5,2) inside W(5,8) (q = 8 points of H(8) = points of PG(5,8), opposite iff B != 0).
Basis: the 7 special points of a 217-set rescaled so that their Gram matrix is J - I (v0..v6, v6 = v0+...+v5),
u_j = v_j (j < 6). Every point gets coordinates c in GF(8)^6 w.r.t. u. Groups act by GF(2)-matrices on c and by
the Frobenius c -> c^2. Uses research/squads/d10D7-r5/c4/common.py (coordinates, B form, GF(8) tables)."""
import numpy as np, sys, itertools
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c4')
from common import V, Bval, MT, INVA, normalize, code, C2I, N
def gmul(a, b): return MT[a, b]
def ginv(a): return INVA[a]
def matvec(M, X):            # M: 6x6 GF(8), X: (n,6) -> (n,6)
    out = np.zeros_like(X)
    for i in range(6):
        acc = np.zeros(len(X), dtype=np.int64)
        for j in range(6): acc ^= MT[M[i, j], X[:, j]]
        out[:, i] = acc
    return out
def mat_inv(A):
    n = len(A); M = [[int(A[i][j]) for j in range(n)] + [int(i == j) for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c]); M[c], M[p] = M[p], M[c]
        iv = int(INVA[M[c][c]]); M[c] = [int(MT[iv, x]) for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [x ^ int(MT[f, y]) for x, y in zip(M[r], M[c])]
    return np.array([row[n:] for row in M], dtype=np.int64)
def special_basis(ids217):
    ids = np.array(sorted(ids217)); P = V[ids]; n = len(ids)
    G = Bval(P[:, None, :], P[None, :, :])
    T = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for j in range(i + 1, n):
            r = MT[G[:, j], INVA[G[:, i]]]; mask = np.ones(n, bool); mask[i] = mask[j] = False
            T[i, j] = T[j, i] = np.bincount(r[mask], minlength=8)[1:].max()
    sp = np.nonzero((T == 65).sum(1) == 6)[0]; g = G[np.ix_(sp, sp)]
    lam = []
    for i in range(7):
        j, k = [x for x in range(7) if x != i][:2]
        l2 = MT[g[j, k], INVA[MT[g[i, j], g[i, k]]]]; lam.append(MT[MT[l2, l2], MT[l2, l2]])   # sqrt = x^4
    vs = np.array([MT[lam[i], P[sp[i]]] for i in range(7)])
    s = np.zeros(6, dtype=np.int64)
    for i in range(7): s ^= vs[i]
    assert not s.any(), 'v0+...+v6 != 0'
    U = vs[:6].T.copy()                      # columns u_j
    return U, mat_inv(U), ids[sp]
def coords(Uinv, X): return matvec(Uinv, X)            # c = U^-1 x
def to_points(U, C):                                     # coordinates -> point ids
    X = matvec(U, C); return C2I[code(normalize(X))]
def perm_from_c_map(U, Uinv, f):
    """permutation of point ids induced by c -> f(c) (f maps (n,6) arrays, must be semilinear and well defined)."""
    C = coords(Uinv, V); return to_points(U, f(C))
def perm_matrix(sig):        # permutation sig of {0..6} acting on v_i -> v_sig(i); return 6x6 GF(2) matrix on c
    M = np.zeros((6, 6), dtype=np.int64)
    for j in range(6):
        t = sig[j]
        if t < 6: M[t, j] ^= 1
        else:
            for k in range(6): M[k, j] ^= 1
    return M
def orbits(perms):
    parent = np.arange(N)
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for p in perms:
        for x in range(N):
            a, b = find(x), find(int(p[x]))
            if a != b: parent[a] = b
    roots = np.array([find(x) for x in range(N)])
    _, lab = np.unique(roots, return_inverse=True)
    return lab

def orbit_graph(lab):
    """orbits from labels; returns sizes, members, selfcompat mask, compat matrix among self-compatible orbits."""
    no = lab.max() + 1; members = [np.nonzero(lab == o)[0] for o in range(no)]
    sizes = np.array([len(m) for m in members])
    sc = np.zeros(no, bool)
    for o, m in enumerate(members):
        X = V[m]; Bm = Bval(X[:, None, :], X[None, :, :]) != 0; np.fill_diagonal(Bm, True); sc[o] = Bm.all()
    S = np.nonzero(sc)[0]
    if len(S) == 0: return sizes, members, S, np.zeros((0, 0), bool)
    order = np.concatenate([members[o] for o in S]); starts = np.concatenate([[0], np.cumsum(sizes[S])[:-1]])
    A = np.zeros((len(S), len(S)), bool)
    for a, o in enumerate(S):
        r = members[o][0]; ok = Bval(V[r][None, :], V) != 0
        A[a] = np.logical_and.reduceat(ok[order], starts)
    A = A & A.T; np.fill_diagonal(A, False)
    return sizes, members, S, A
def max_weight_clique(A, w, time_limit=60.0):
    """exact branch and bound (greedy colouring bound); returns (best weight, list of indices)."""
    import time
    n = len(w); t0 = time.time(); best = [0, []]
    nb = [set(np.nonzero(A[i])[0].tolist()) for i in range(n)]
    def colour_bound(cand):
        # greedy colouring: each colour class bound by its max weight
        cand = sorted(cand, key=lambda i: -w[i]); classes = []
        for v in cand:
            for c in classes:
                if not (nb[v] & c[0]): c[0].add(v); break
            else: classes.append([{v}])
        return sum(max(w[i] for i in c[0]) for c in classes)
    def expand(cur, curw, cand):
        if time.time() - t0 > time_limit: return
        if curw > best[0]: best[0] = curw; best[1] = list(cur)
        if not cand: return
        if curw + colour_bound(cand) <= best[0]: return
        for v in sorted(cand, key=lambda i: -w[i]):
            if curw + sum(w[i] for i in cand) <= best[0]: return
            expand(cur + [v], curw + w[v], cand & nb[v]); cand = cand - {v}
    expand([], 0, set(range(n)))
    return best[0], best[1], time.time() - t0 < time_limit
