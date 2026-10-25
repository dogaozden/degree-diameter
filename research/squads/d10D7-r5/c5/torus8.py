# c5: H(8) orbit-clique search. Group = cyclic torus T = diag(A, A^{-T}) on V=GF(8)^6 (J=[[0,I],[I,0]]),
# A = blockdiag(M_lam, 1), M_lam = mult by lam in GF(64)=GF(8)(t), t^2+t+beta=0. Orbits on PG(5,8), self-compatible
# orbits, compatibility, exact max-weight clique. Writes best set as hex_q8 point ids.
import numpy as np, sys, time, pickle
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d10D7-r5/c5')
from gf8 import *
q, N, X8 = load_hex8()
P6 = pickle.load(open('/home/user/degree-diameter/research/squads/d10D7-r5/c5/sp62_orbits8.pkl', 'rb'))[0]
pw8 = 8 ** np.arange(6)
idx6 = np.full(8 ** 6, -1, dtype=np.int64); idx6[P6 @ pw8] = np.arange(len(P6))
def ginv(A):  # GF(8) matrix inverse (Gauss-Jordan)
    n = A.shape[0]; M = np.concatenate([A.copy(), np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        piv = next(i for i in range(c, n) if M[i, c])
        M[[c, piv]] = M[[piv, c]]
        M[c] = MUL[INV[M[c, c]], M[c]]
        for i in range(n):
            if i != c and M[i, c]: M[i] ^= MUL[M[i, c], M[c]]
    return M[:, n:]
def matmul(A, B):
    n, k = A.shape; k2, m = B.shape
    out = np.zeros((n, m), dtype=np.int64)
    for i in range(n):
        for j in range(m):
            acc = 0
            for t in range(k): acc ^= MUL[A[i, t], B[t, j]]
            out[i, j] = acc
    return out
def torus_gen(beta, a, b):
    # mult by lam = a + b t: columns (a, b), (b*beta, a+b)
    Ml = np.array([[a, MUL[b, beta]], [b, a ^ b]], dtype=np.int64)
    A = np.zeros((3, 3), dtype=np.int64); A[:2, :2] = Ml; A[2, 2] = 1
    AiT = ginv(A).T
    T = np.zeros((6, 6), dtype=np.int64); T[:3, :3] = A; T[3:, 3:] = AiT
    return T
def proj_order(T):
    I = np.eye(6, dtype=np.int64); P = T.copy(); k = 1
    while not np.array_equal(P, I):
        P = matmul(P, T); k += 1
        if k > 1000: return -1
    return k
def perm_of(T):
    Y = np.zeros((len(P6), 6), dtype=np.int64)
    for i in range(6):
        acc = np.zeros(len(P6), dtype=np.int64)
        for j in range(6):
            if T[i, j]: acc ^= MUL[T[i, j], P6[:, j]]
        Y[:, i] = acc
    Yn = normalize_rows(Y)
    return idx6[Yn @ pw8]
J6 = np.zeros((6, 6), dtype=np.int64)
for i in range(3): J6[i, i + 3] = 1; J6[i + 3, i] = 1
def omega_rows(X, Y):   # (a,6),(b,6) -> (a,b) GF(8) symplectic form (char 2, J has 0/1 entries)
    acc = np.zeros((X.shape[0], Y.shape[0]), dtype=np.int64)
    for i in range(3):
        acc ^= MUL[X[:, i][:, None], Y[:, i + 3][None, :]] ^ MUL[X[:, i + 3][:, None], Y[:, i][None, :]]
    return acc
def cover_orbits(gens):
    M = len(P6); parent = np.arange(M)
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for g in gens:
        pm = perm_of(g)
        for x in range(M):
            a, b = find(x), find(int(pm[x]))
            if a != b: parent[a] = b
    roots = np.array([find(x) for x in range(M)])
    return roots
def run(gens, tag, tlimit=300):
    roots = cover_orbits(gens)
    from collections import Counter
    cnt = Counter(roots.tolist())
    orbs = {}
    for x, r in enumerate(roots.tolist()): orbs.setdefault(r, []).append(x)
    orbs = list(orbs.values())
    print(tag, 'orbit sizes', sorted(Counter(len(o) for o in orbs).items()), flush=True)
    selfok = []
    for o in orbs:
        X = P6[o]; Bm = omega_rows(X, X); np.fill_diagonal(Bm, 1)
        if (Bm != 0).all(): selfok.append(o)
    print(tag, 'self-compatible orbits:', [len(o) for o in selfok], flush=True)
    if not selfok: return None
    M = len(selfok); A = np.zeros((M, M), dtype=bool)
    reps = [P6[o[0]][None, :] for o in selfok]
    for i in range(M):
        for j in range(i + 1, M):
            ok = (omega_rows(reps[i], P6[selfok[j]]) != 0).all()
            A[i, j] = A[j, i] = ok
    w = [len(o) for o in selfok]
    best = [0, []]; t0 = time.time()
    def bb(cand, cur, cw):
        if cw > best[0]: best[0] = cw; best[1] = list(cur)
        if not cand or time.time() - t0 > tlimit: return
        if cw + sum(w[c] for c in cand) <= best[0]: return
        for k, c in enumerate(cand):
            rest = [d for d in cand[k + 1:] if A[c, d]]
            if cw + w[c] + sum(w[d] for d in rest) <= best[0]: continue
            bb(rest, cur + [c], cw + w[c])
    bb(list(range(M)), [], 0)
    print(tag, 'best clique weight', best[0], 'orbits', [w[c] for c in best[1]], 'time', round(time.time() - t0, 1), flush=True)
    pts = [int(x) for c in best[1] for x in selfok[c]]
    return pts
def to_hex_ids(pts):
    v = P6[pts]
    X3 = SQ4[MUL[v[:, 0], v[:, 3]] ^ MUL[v[:, 1], v[:, 4]] ^ MUL[v[:, 2], v[:, 5]]]
    X7 = np.stack([v[:, 0], v[:, 1], v[:, 2], X3, v[:, 3], v[:, 4], v[:, 5]], axis=1)
    assert (normalize_rows(X7) == X7).all()
    assert (MUL[X7[:, 0], X7[:, 4]] ^ MUL[X7[:, 1], X7[:, 5]] ^ MUL[X7[:, 2], X7[:, 6]] == MUL[X3, X3]).all()
    code = X7 @ (8 ** np.arange(7))
    idx7 = np.full(8 ** 7, -1, dtype=np.int64); idx7[X8 @ (8 ** np.arange(7))] = np.arange(N)
    ids = idx7[code]
    assert (ids >= 0).all()
    return ids
if __name__ == '__main__':
    # GF(64) = GF(8)(t), t^2+t+beta irreducible over GF(8): absolute trace of beta is 1
    tr = lambda z: z ^ MUL[z, z] ^ MUL[MUL[z, z], MUL[z, z]]
    beta = next(z for z in range(8) if tr(z) == 1)
    # generator lam with projective order 63 (lam not in GF(8))
    lam = None
    for a in range(8):
        for b in range(1, 8):
            T = torus_gen(beta, a, b)
            if proj_order(T) == 63: lam = (a, b, T); break
        if lam: break
    print('beta', beta, 'lam', lam[:2], 'order', proj_order(lam[2]), flush=True)
    res = {}
    res['C63'] = run([lam[2]], 'C63')
    # subgroup C9 and C7 (orders divisors) for comparison
    T9 = matmul(matmul(lam[2], lam[2]), matmul(lam[2], lam[2]))  # placeholder, replaced below
    pickle.dump(res, open('/home/user/degree-diameter/research/squads/d10D7-r5/c5/torus8_res.pkl', 'wb'))
