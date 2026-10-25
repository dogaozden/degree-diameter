"""c5 common tools: H(q) points of Q(6,q) (q=5 or 7), polar form B, E7 root data, orbits, orbit graphs.
B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3 (mod q). Points opposite iff B != 0."""
import struct, numpy as np, itertools, random, os
HEXDIR = '/home/user/degree-diameter/research/d10D7/hex/'
def load_hex(q):
    b = open(HEXDIR + 'hex_q%d.bin' % q, 'rb').read()
    qq, N, L = struct.unpack('3i', b[:12]); assert qq == q
    LP = np.frombuffer(b[12:12 + 4 * L * (q + 1)], dtype='<i4').reshape(L, q + 1).astype(np.int64)
    C = np.frombuffer(b[12 + 4 * L * (q + 1):12 + 4 * L * (q + 1) + 7 * N], dtype=np.uint8).reshape(N, 7).astype(np.int64)
    return dict(q=q, N=N, L=L, LP=LP, C=C)
A7 = np.zeros((7, 7), dtype=np.int64)
for _i, _j in [(0, 4), (1, 5), (2, 6)]: A7[_i, _j] = A7[_j, _i] = 1
A7[3, 3] = -2
def bform_mat(X, Y, q):
    """B(x,y) matrix for row arrays X (n,7), Y (m,7) -> (n,m) mod q"""
    return (X @ A7 @ Y.T) % q
def make_normalizer(q):
    inv = {a: pow(a, q - 2, q) for a in range(1, q)}
    def normalize(M):
        M = np.array(M, dtype=np.int64) % q
        out = np.empty_like(M)
        for r in range(M.shape[0]):
            nz = np.nonzero(M[r])[0]
            if len(nz) == 0: out[r] = 0; continue
            out[r] = (M[r] * inv[int(M[r, nz[0]])]) % q
        return out
    return normalize
class Geo:
    def __init__(self, q):
        self.q = q; h = load_hex(q); self.h = h
        self.N = h['N']; self.C = h['C']; self.LP = h['LP']; self.L = h['L']
        self.normalize = make_normalizer(q)
        self.code = {tuple(r): i for i, r in enumerate(self.C.tolist())}
        self.PL = [[] for _ in range(self.N)]
        for l in range(self.L):
            for p in self.LP[l]: self.PL[p].append(l)
    def perm_of_matrix(self, M):
        """permutation of point ids induced by the linear map x -> M x (M 7x7 mod q); must preserve Q"""
        q = self.q
        Y = self.normalize((self.C @ np.asarray(M, dtype=np.int64).T) % q)
        perm = np.array([self.code[tuple(r)] for r in Y.tolist()], dtype=np.int64)
        assert len(set(perm.tolist())) == self.N
        return perm
    def is_isometry(self, M):
        q = self.q; M = np.asarray(M, dtype=np.int64) % q
        return bool(((M.T @ A7 @ M - A7) % q == 0).all())
def orbits_from_perms(N, perms):
    parent = np.arange(N)
    def find(x):
        r = x
        while parent[r] != r: r = parent[r]
        while parent[x] != r: parent[x], x = r, parent[x]
        return r
    for p in perms:
        for x in range(N):
            a, b = find(x), find(int(p[x]))
            if a != b: parent[a] = b
    roots = np.array([find(x) for x in range(N)])
    _, lab = np.unique(roots, return_inverse=True)
    return lab
def orbit_info(G, lab, Bq=None):
    """returns list of member arrays, self-compatible flags, and compat bitsets (python ints) among selfcompat orbits.
    compat(O1,O2) iff all cross pairs opposite (B != 0)."""
    q = G.q; C = G.C
    no = lab.max() + 1
    members = [np.nonzero(lab == o)[0] for o in range(no)]
    sc = []
    for m in members:
        Bm = bform_mat(C[m], C[m], q) != 0
        np.fill_diagonal(Bm, True)
        sc.append(bool(Bm.all()))
    S = [o for o in range(no) if sc[o]]
    # opposite matrix from representative: for orbit a (rep r) and point set of orbit b
    opp_rep = {}
    for o in S:
        r = members[o][0]
        opp_rep[o] = (bform_mat(C[r][None, :], C, q)[0] != 0)  # bool over all points
    M = {}
    for a in S:
        ok = opp_rep[a]
        row = []
        for b in S:
            row.append(bool(ok[members[b]].all()))
        M[a] = row
    return members, S, M
