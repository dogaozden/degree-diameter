# c4 (round 5): shared tools. Points of H(8) = PG(5,8) with coordinates v = (x0,x1,x2,x4,x5,x6) (Tits coords,
# nucleus x3 dropped), normalised (first nonzero = 1). Opposite iff B(v,w) != 0,
# B = v0 w3 + v3 w0 + v1 w4 + v4 w1 + v2 w5 + v5 w2 (char 2). GF(8) = GF(2)[x]/(x^3+x+1), element a0+2a1+4a2.
import numpy as np, struct
HEX = '/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin'
N = 37449
def _hm(a, b):
    r = 0
    for i in range(3):
        if (b >> i) & 1: r ^= a << i
    for i in (4, 3):
        if (r >> i) & 1: r ^= 0b1011 << (i - 3)
    return r
MT = np.array([[_hm(a, b) for b in range(8)] for a in range(8)], dtype=np.int64)
INVA = np.zeros(8, dtype=np.int64)
for a in range(1, 8):
    for b in range(1, 8):
        if MT[a, b] == 1: INVA[a] = b
POW8 = 8 ** np.arange(6)

def normalize(V):
    V = np.asarray(V, dtype=np.int64)
    first = np.argmax(V != 0, axis=1)
    lead = V[np.arange(len(V)), first]
    return MT[INVA[lead][:, None], V]

def code(V):
    return np.asarray(V, dtype=np.int64) @ POW8

def load_points():
    with open(HEX, 'rb') as f:
        q, n, L = struct.unpack('3i', f.read(12)); f.seek(12 + 4 * n * (q + 1))
        P = np.frombuffer(f.read(7 * n), dtype=np.uint8).reshape(n, 7).astype(np.int64)
    V = normalize(P[:, [0, 1, 2, 4, 5, 6]])
    c2i = np.full(8 ** 6, -1, dtype=np.int64)
    c2i[code(V)] = np.arange(n)
    assert (c2i[code(V)] == np.arange(n)).all() and len(set(code(V).tolist())) == n
    return V, c2i

V, C2I = load_points()

def Bval(A, Bv):
    """A, Bv: arrays (...,6) broadcastable. Returns GF(8) value of the symplectic form."""
    return (MT[A[..., 0], Bv[..., 3]] ^ MT[A[..., 3], Bv[..., 0]] ^ MT[A[..., 1], Bv[..., 4]]
            ^ MT[A[..., 4], Bv[..., 1]] ^ MT[A[..., 2], Bv[..., 5]] ^ MT[A[..., 5], Bv[..., 2]])

def perm_from_matrix(G):
    """Permutation of point ids induced by v -> G v (G: 6x6 over GF(8)); must map points to points."""
    G = np.asarray(G, dtype=np.int64)
    W = np.zeros_like(V)
    for i in range(6):
        acc = np.zeros(N, dtype=np.int64)
        for j in range(6):
            acc ^= MT[G[i, j], V[:, j]]
        W[:, i] = acc
    assert (W != 0).any(axis=1).all()
    ids = C2I[code(normalize(W))]
    assert (ids >= 0).all()
    assert len(set(ids.tolist())) == N, 'not a bijection'
    return ids

def perm_frobenius():
    """coordinatewise squaring: a semilinear isometry of B."""
    W = MT[V, V]
    return C2I[code(normalize(W))]

def mat_mul(A, B):
    n = len(A); C = np.zeros((n, n), dtype=np.int64)
    for i in range(n):
        for j in range(n):
            s = 0
            for k in range(n): s ^= MT[A[i][k], B[k][j]]
            C[i, j] = s
    return C

def inv_transpose(A):
    """inverse transpose over GF(8) by Gauss-Jordan."""
    n = len(A); M = [[int(A[i][j]) for j in range(n)] + [1 if i == j else 0 for j in range(n)] for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c])
        M[c], M[p] = M[p], M[c]
        iv = int(INVA[M[c][c]]); M[c] = [int(MT[iv, x]) for x in M[c]]
        for r in range(n):
            if r != c and M[r][c]:
                f = M[r][c]; M[r] = [x ^ int(MT[f, y]) for x, y in zip(M[r], M[c])]
    Ainv = [row[n:] for row in M]
    return [[Ainv[j][i] for j in range(n)] for i in range(n)]   # transpose of inverse

def orbits_from_perms(perms):
    orb = np.full(N, -1, dtype=np.int64); members = []
    for s in range(N):
        if orb[s] >= 0: continue
        k = len(members); comp = [s]; orb[s] = k; i = 0
        while i < len(comp):
            x = comp[i]; i += 1
            for p in perms:
                y = int(p[x])
                if orb[y] < 0: orb[y] = k; comp.append(y)
        members.append(np.array(comp, dtype=np.int64))
    return orb, members

def selfcompat(members):
    ok = np.zeros(len(members), dtype=bool)
    for k, mem in enumerate(members):
        if len(mem) == 1: ok[k] = True; continue
        Vm = V[mem]
        Bm = Bval(Vm[:, None, :], Vm[None, :, :]) != 0
        np.fill_diagonal(Bm, True)
        ok[k] = bool(Bm.all())
    return ok

def compat_matrix(S_idx, members):
    """A[i,j] = True iff every point of orbit S_idx[i] is opposite to every point of orbit S_idx[j]."""
    order = np.concatenate(members)
    sizes = np.array([len(m) for m in members]); starts = np.concatenate([[0], np.cumsum(sizes)[:-1]])
    S_idx = np.asarray(S_idx)
    A = np.zeros((len(S_idx), len(S_idx)), dtype=bool)
    for ii, k in enumerate(S_idx):
        r = members[k][0]
        vals = Bval(V[r][None, :], V) != 0
        comp = np.logical_and.reduceat(vals[order], starts)
        A[ii] = comp[S_idx]
    A = A & A.T
    np.fill_diagonal(A, False)
    return A

def write_mis_graph(path, S_idx, members, A):
    """Binary CSR of the CONFLICT graph (non-adjacent in A) for mis_csr: header n,m; mem; off; nb."""
    n = len(S_idx); m = len(members[S_idx[0]])
    assert all(len(members[k]) == m for k in S_idx)
    mem = np.array([members[k] for k in S_idx], dtype=np.int32).reshape(-1)
    conf = ~A; np.fill_diagonal(conf, False)
    deg = conf.sum(1); off = np.concatenate([[0], np.cumsum(deg)]).astype(np.int32)
    nb = np.concatenate([np.nonzero(conf[i])[0] for i in range(n)]).astype(np.int32)
    with open(path, 'wb') as f:
        np.array([n, m], dtype=np.int32).tofile(f); mem.tofile(f); off.tofile(f); nb.tofile(f)

def check_set(ids):
    ids = np.asarray(sorted(set(int(x) for x in ids)), dtype=np.int64)
    M = Bval(V[ids][:, None, :], V[ids][None, :, :]) != 0
    np.fill_diagonal(M, True)
    return bool(M.all()), len(ids)

def write_ids(path, ids):
    open(path, 'w').write(' '.join(map(str, sorted(int(x) for x in ids))) + '\n')
