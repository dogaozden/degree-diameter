# c12 helper: field tables, hexagon loading, monomial/Frobenius collineations, free subgroups, quotients.
import numpy as np, sys, itertools
from collections import deque

def field_tables(q):
    p = next(d for d in range(2, q + 1) if q % d == 0)
    e = 0; pe = 1
    while pe < q: pe *= p; e += 1
    cpoly = {4: [1, 1], 8: [1, 1, 0], 9: [1, 0], 16: [1, 1, 0, 0], 25: [2, 0], 27: [1, 2, 0], 32: [1, 0, 1, 0, 0]}
    c = cpoly.get(q, [1, 0, 0, 0, 0]) if e > 1 else [0] * e
    if e == 1:
        ADD = np.array([[(a + b) % p for b in range(q)] for a in range(q)])
        MUL = np.array([[(a * b) % p for b in range(q)] for a in range(q)])
    else:
        def digits(x): return [(x // p ** i) % p for i in range(e)]
        def val(d): return sum(d[i] * p ** i for i in range(e))
        ADD = np.zeros((q, q), dtype=np.int64); MUL = np.zeros((q, q), dtype=np.int64)
        for x in range(q):
            for y in range(q):
                a, b = digits(x), digits(y)
                ADD[x, y] = val([(a[i] + b[i]) % p for i in range(e)])
                r = [0] * (2 * e)
                for i in range(e):
                    for j in range(e):
                        r[i + j] = (r[i + j] + a[i] * b[j]) % p
                for k in range(2 * e - 2, e - 1, -1):
                    f = r[k]; r[k] = 0
                    for i in range(e):
                        r[k - e + i] = (r[k - e + i] - f * c[i]) % p
                MUL[x, y] = val(r[:e])
    NEG = np.array([int(np.where(ADD[x] == 0)[0][0]) for x in range(q)])
    INV = np.array([-1] + [int(np.where(MUL[x] == 1)[0][0]) for x in range(1, q)])
    # Frobenius x -> x^p as a table
    FROB = np.array([1 if x == 0 else x for x in range(q)])
    frob = np.arange(q)
    for x in range(q):
        y = 1
        for _ in range(p): y = MUL[y, x]
        frob[x] = y
    return p, e, ADD, MUL, NEG, INV, frob

class Hex:
    def __init__(self, path):
        raw = np.fromfile(path, dtype=np.int32, count=3)
        self.q, self.N, self.L = int(raw[0]), int(raw[1]), int(raw[2])
        body = np.fromfile(path, dtype=np.int32)[3:]
        self.lines = body[:self.L * (self.q + 1)].reshape(self.L, self.q + 1).astype(np.int64)
        self.coords = np.fromfile(path, dtype=np.uint8, offset=4 * (3 + self.L * (self.q + 1)), count=self.N * 7).reshape(self.N, 7).astype(np.int64)
        self.p, self.e, self.ADD, self.MUL, self.NEG, self.INV, self.frob = field_tables(self.q)
        pw = self.q ** np.arange(7, dtype=np.int64)
        self.codes = self.coords @ pw
        assert np.all(np.diff(self.codes) > 0)
        rng = np.random.default_rng(12345)
        self.w = rng.integers(1, 2**62, size=self.N, dtype=np.int64)  # point hash weights
        self.linehash = self.w[self.lines].sum(axis=1)  # wraps mod 2^64
        self.lsort = np.argsort(self.linehash); self.lhs = self.linehash[self.lsort]
        # point -> lines
        self.inc = [[] for _ in range(self.N)]
        for l in range(self.L):
            for p_ in self.lines[l]: self.inc[p_].append(l)
        self.inc = np.array(self.inc, dtype=np.int64)

    def normalize_rows(self, Y):
        q = self.q
        nz = Y != 0
        first = np.argmax(nz, axis=1)
        lead = Y[np.arange(Y.shape[0]), first]
        s = self.INV[lead]
        return self.MUL[s[:, None], Y]

    def map_points(self, perm_idx, d, frobk):
        """monomial map Y_i = d_i * X_{perm_idx[i]} then Frobenius^frobk; returns point id array or None."""
        X = self.coords
        Y = self.MUL[np.asarray(d)[None, :], X[:, perm_idx]]
        for _ in range(frobk):
            Y = self.frob[Y]
        Y = self.normalize_rows(Y)
        c = Y @ (self.q ** np.arange(7, dtype=np.int64))
        idx = np.searchsorted(self.codes, c)
        idx = np.minimum(idx, self.N - 1)
        if not np.all(self.codes[idx] == c):
            return None
        return idx

    def line_perm(self, pperm):
        """given a point permutation, return the induced line permutation or None if not a collineation."""
        h = self.w[pperm[self.lines]].sum(axis=1)
        ls = np.searchsorted(self.lhs, h)
        ls = np.minimum(ls, self.L - 1)
        if not np.all(self.lhs[ls] == h):
            return None
        return self.lsort[ls]

def fixed_free(pperm, lperm):
    return not (np.any(pperm == np.arange(len(pperm))) or np.any(lperm == np.arange(len(lperm))))

def orbit_quotient(hx, gens_elems):
    """gens_elems: list of (pperm, lperm) forming a free group (all elements). Returns (nq, adjacency lists, quotient diameter)."""
    N, L = hx.N, hx.L
    vp = np.concatenate([np.arange(N), np.arange(L)])
    orb = np.arange(N + L)
    for pp, lp in gens_elems:
        full = np.concatenate([pp, N + lp])
        orb = np.minimum(orb, full)
    # orb[v] is min over group orbit of v (group closed under composition; gens_elems is the full group)
    reps, lab = np.unique(orb, return_inverse=True)
    nq = len(reps)
    # edges
    pv = np.repeat(np.arange(N), hx.inc.shape[1])
    lv = N + hx.inc.reshape(-1)
    a = lab[pv]; b = lab[lv]
    ok = a != b  # cannot be a loop: points and lines of different type are never in same orbit under type-preserving group
    E = set(zip(np.minimum(a, b)[ok].tolist(), np.maximum(a, b)[ok].tolist()))
    return nq, E

def quotient_diameter(nq, E):
    from scipy.sparse import coo_matrix
    from scipy.sparse.csgraph import shortest_path
    if not E: return None, None
    r = [x for x, y in E] + [y for x, y in E]; c = [y for x, y in E] + [x for x, y in E]
    G = coo_matrix((np.ones(len(r)), (r, c)), shape=(nq, nq)).tocsr()
    D = shortest_path(G, unweighted=True, directed=False)
    deg = np.bincount(np.array(r), minlength=nq)
    return int(np.max(D)) if np.all(np.isfinite(D)) else -1, int(deg.max())
