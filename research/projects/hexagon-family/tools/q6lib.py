"""q6lib: shared helpers for the hexagon-family project (partial ovoids of Q(6,q) inside H(q)).

Points of H(q) = points of Q(6,q): x0x4 + x1x5 + x2x6 - x3^2 = 0 in PG(6,q), indexed as in hexgen2 (hex/hex_q{q}.bin).
Polar form B(x,y) = x0y4+x4y0+x1y5+x5y1+x2y6+x6y2-2x3y3. Two points are OPPOSITE in H(q) (distance 6) iff B != 0,
so a pairwise opposite set = a partial ovoid of Q(6,q) (all pairs non-orthogonal). Field elements are ints
0..q-1 encoded as in hexgen2 (a0 + a1 p + ..., fixed irreducible); for prime q this is ordinary arithmetic mod q.

    import sys; sys.path.insert(0, '<project>/tools'); from q6lib import Geo
    G = Geo(11)                  # loads hex/hex_q11.bin
    G.N, G.C (N x 7 coords), G.LP (L x (q+1) point ids), G.PL (N x (q+1) line ids)
    G.B(X, Y)                    # matrix of polar form values for coordinate rows X (n,7), Y (m,7)
    G.opp_matrix(ids)            # boolean matrix, True = opposite
    G.ids_of(V)                  # point ids of (nonzero, singular) row vectors V (normalised internally)
    G.perm(M)                    # permutation of point ids induced by x -> M x (M 7x7 isometry in our coordinates)
    G.to_std(Gram)               # T with T^t A7 T = c*Gram (q odd): maps an abstract quadratic space onto ours
    G.check_opp(ids)             # (ok, number of outside points opposite to all)
"""
import struct, numpy as np, os, random
HERE = os.path.dirname(os.path.abspath(__file__))
HEXDIR = os.path.join(os.path.dirname(HERE), 'hex')
IRRED = {4: [1, 1], 8: [1, 1, 0], 9: [1, 0], 16: [1, 1, 0, 0], 25: [2, 0], 27: [1, 2, 0], 32: [1, 0, 1, 0, 0]}

def field_tables(q):
    p = 2
    while q % p: p += 1
    e = 1
    while p ** e < q: e += 1
    c = IRRED.get(q, [0] * e)
    ADD = np.zeros((q, q), dtype=np.int64); MUL = np.zeros((q, q), dtype=np.int64)
    def digits(x): return [(x // p ** i) % p for i in range(e)]
    for x in range(q):
        a = digits(x)
        for y in range(q):
            b = digits(y)
            ADD[x, y] = sum(((a[i] + b[i]) % p) * p ** i for i in range(e))
            r = [0] * (2 * e)
            for i in range(e):
                for j in range(e): r[i + j] = (r[i + j] + a[i] * b[j]) % p
            for k in range(2 * e - 2, e - 1, -1):
                f = r[k]
                if f:
                    r[k] = 0
                    for i in range(e): r[k - e + i] = (r[k - e + i] - f * c[i]) % p
            MUL[x, y] = sum(r[i] * p ** i for i in range(e))
    NEG = np.array([int(np.nonzero(ADD[x] == 0)[0][0]) for x in range(q)])
    INV = np.array([0] + [int(np.nonzero(MUL[x] == 1)[0][0]) for x in range(1, q)])
    return p, e, ADD, MUL, NEG, INV

A7 = np.zeros((7, 7), dtype=np.int64)
for _i, _j in [(0, 4), (1, 5), (2, 6)]: A7[_i, _j] = A7[_j, _i] = 1
A7[3, 3] = -2   # polar form matrix (Q(x) = x^t A7 x / 2 for odd q)

class Geo:
    def __init__(self, q, hexdir=HEXDIR):
        self.q = q
        b = open(os.path.join(hexdir, 'hex_q%d.bin' % q), 'rb').read()
        qq, N, L = struct.unpack('3i', b[:12]); assert qq == q
        o = 12; self.LP = np.frombuffer(b[o:o + 4 * L * (q + 1)], dtype='<i4').reshape(L, q + 1).astype(np.int64)
        o += 4 * L * (q + 1); self.C = np.frombuffer(b[o:o + 7 * N], dtype=np.uint8).reshape(N, 7).astype(np.int64)
        self.N, self.L = N, L
        PL = np.zeros((N, q + 1), dtype=np.int64); cnt = np.zeros(N, dtype=np.int64)
        for l in range(L):
            for pt in self.LP[l]: PL[pt, cnt[pt]] = l; cnt[pt] += 1
        self.PL = PL
        self.p, self.e, self.ADD, self.MUL, self.NEG, self.INV = field_tables(q)
        self.prime = (self.e == 1)
        self.pw = q ** np.arange(7, dtype=np.int64)
        self.codes = (self.C * self.pw).sum(1)          # increasing (hexgen2 order)
        assert (np.diff(self.codes) > 0).all()

    # ---- field helpers (vectorised, work for prime powers via tables) ----
    def fadd(self, a, b): return (a + b) % self.q if self.prime else self.ADD[a, b]
    def fmul(self, a, b): return (a * b) % self.q if self.prime else self.MUL[a, b]
    def fneg(self, a): return (-a) % self.q if self.prime else self.NEG[a]

    def matmul(self, X, Y):
        """X (n,k) @ Y (k,m) over GF(q)"""
        X = np.asarray(X, dtype=np.int64); Y = np.asarray(Y, dtype=np.int64)
        if self.prime: return (X @ Y) % self.q
        n, k = X.shape; m = Y.shape[1]; out = np.zeros((n, m), dtype=np.int64)
        for i in range(k): out = self.ADD[out, self.MUL[X[:, i][:, None], Y[i][None, :]]]
        return out

    def B(self, X, Y):
        """polar form values B(x, y) for rows of X (n,7) and Y (m,7)"""
        X = np.asarray(X, dtype=np.int64); Y = np.asarray(Y, dtype=np.int64)
        if self.prime: return (X @ A7 @ Y.T) % self.q
        A = np.zeros((7, 7), dtype=np.int64)
        for i, j in [(0, 4), (1, 5), (2, 6)]: A[i, j] = A[j, i] = 1
        A[3, 3] = self.fneg(self.fadd(1, 1))
        return self.matmul(self.matmul(X, A), Y.T)

    def opp_matrix(self, ids):
        X = self.C[np.asarray(ids)]; return self.B(X, X) != 0

    def normalize(self, V):
        V = np.asarray(V, dtype=np.int64) % self.q if self.prime else np.asarray(V, dtype=np.int64)
        nz = V != 0; first = np.argmax(nz, axis=1); lead = V[np.arange(len(V)), first]
        inv = self.INV[lead]
        return self.fmul(V, inv[:, None]) if self.prime else self.MUL[V, inv[:, None]]

    def ids_of(self, V):
        W = self.normalize(V); c = (W * self.pw).sum(1)
        idx = np.searchsorted(self.codes, c)
        idx = np.minimum(idx, self.N - 1)
        if not (self.codes[idx] == c).all(): raise ValueError('vector not a point of Q(6,q)')
        return idx

    def perm(self, M):
        """permutation of point ids for x -> M x (M must preserve Q up to a scalar)"""
        Y = self.matmul(self.C, np.asarray(M, dtype=np.int64).T)
        return self.ids_of(Y)

    def check_opp(self, ids):
        ids = np.asarray(ids); O = self.opp_matrix(ids); np.fill_diagonal(O, True)
        ok = bool(O.all())
        Bm = self.B(self.C, self.C[ids]) != 0
        inset = np.zeros(self.N, dtype=bool); inset[ids] = True
        ext = int((Bm.all(1) & ~inset).sum())
        return ok, ext

    def to_std(self, Gram):
        """q odd prime only: return T (7x7) with T^t A7 T = c * Gram for some c != 0; then x -> T x maps vectors of
        the abstract space (Gram) to our coordinates, and an abstract isometry g becomes T g T^-1."""
        q = self.q; assert self.prime and q % 2 == 1
        G = np.asarray(Gram, dtype=np.int64) % q
        rng = random.Random(1)
        def form(u, v): return int(u @ G @ v) % q
        basis = []   # build hyperbolic pairs (e, f) with form(e,e)=form(f,f)=0, form(e,f)=1
        def perp_space(vs):
            # null space of rows [v^t G] for v in vs
            if not vs: return [np.eye(7, dtype=np.int64)[i] for i in range(7)]
            Mrows = np.array([(v @ G) % q for v in vs]); return nullspace_mod(Mrows, q)
        for _ in range(3):
            S = perp_space(basis)
            while True:   # random isotropic vector in span S
                coef = np.array([rng.randrange(q) for _ in S]); v = (coef @ np.array(S)) % q
                if v.any() and form(v, v) == 0: break
            while True:
                coef = np.array([rng.randrange(q) for _ in S]); w = (coef @ np.array(S)) % q
                if form(v, w) != 0: break
            w = (w * pow(form(v, w), q - 2, q)) % q
            w = (w - (form(w, w) * pow(2, q - 2, q)) * v) % q   # now form(w,w)=0, form(v,w)=1
            basis += [v, w]
        S = perp_space(basis); z = np.array(S[0]) % q; a = form(z, z)   # anisotropic
        # our space: e_i=(unit i), f_i=(unit i+4), B(e_i,f_i)=1, and the 4th vector u3 with B(u3,u3)=-2.
        # Gram in abstract basis (v1,w1,v2,w2,v3,w3,z) is diag(H,H,H,a); ours in (e0,e4,e1,e5,e2,e6,e3) is diag(H,H,H,-2).
        # scale: c*Gram should match ours; choose c with c*a = -2*s^2 i.e. need (-2/a)/c square; take c with c*H~H via
        # scaling w's by c^-1. Pick c = -2 * a^-1 * s^2 with s=1: c = -2/a.
        c = (-2 * pow(a, q - 2, q)) % q
        T_abs = np.zeros((7, 7), dtype=np.int64)   # columns: abstract basis vectors in abstract coords
        cols = [basis[0], basis[1], basis[2], basis[3], basis[4], basis[5], z]
        # ours: target positions e0,e4,e1,e5,e2,e6,e3 ; scale w_i by c so that c*form(v,w)=1 -> use w' = w/c? we want
        # c*Gram(v, w') = 1 with w' = w * c^-1 ... handled below by building U mapping ours->abstract.
        U = np.zeros((7, 7), dtype=np.int64)   # U: our coords -> abstract coords; U^t Gram U = c^-1 * A7
        ci = pow(c, q - 2, q)
        tgt = [0, 4, 1, 5, 2, 6, 3]
        for k, (vec, pos) in enumerate(zip(cols, tgt)):
            vv = vec % q
            if k in (1, 3, 5): vv = (vv * ci) % q
            U[:, pos] = vv
        chk = (U.T @ G @ U) % q
        assert ((chk - (ci * A7) % q) % q == 0).all(), 'to_std failed'
        T = inv_mod(U, q)
        return T

def nullspace_mod(M, q):
    M = np.array(M, dtype=np.int64) % q; rows, cols = M.shape; piv = []; r = 0
    for c in range(cols):
        s = next((i for i in range(r, rows) if M[i, c]), None)
        if s is None: continue
        M[[r, s]] = M[[s, r]]; M[r] = (M[r] * pow(int(M[r, c]), q - 2, q)) % q
        for i in range(rows):
            if i != r and M[i, c]: M[i] = (M[i] - M[i, c] * M[r]) % q
        piv.append(c); r += 1
        if r == rows: break
    free = [c for c in range(cols) if c not in piv]; out = []
    for f in free:
        v = np.zeros(cols, dtype=np.int64); v[f] = 1
        for i, pc in enumerate(piv): v[pc] = (-M[i, f]) % q
        out.append(v)
    return out

def inv_mod(M, q):
    n = len(M); A = np.concatenate([np.array(M, dtype=np.int64) % q, np.eye(n, dtype=np.int64)], axis=1)
    for c in range(n):
        s = next(i for i in range(c, n) if A[i, c]); A[[c, s]] = A[[s, c]]
        A[c] = (A[c] * pow(int(A[c, c]), q - 2, q)) % q
        for i in range(n):
            if i != c and A[i, c]: A[i] = (A[i] - A[i, c] * A[c]) % q
    return A[:, n:]

def orbits(N, perms):
    """orbit labels (0..k-1) of the group generated by permutations perms (arrays of length N)"""
    parent = np.arange(N)
    def find(x):
        while parent[x] != x: parent[x] = parent[parent[x]]; x = parent[x]
        return x
    for pm in perms:
        for x in range(N):
            a, b = find(x), find(int(pm[x]))
            if a != b: parent[a] = b
    roots = np.array([find(x) for x in range(N)]); _, lab = np.unique(roots, return_inverse=True)
    return lab
