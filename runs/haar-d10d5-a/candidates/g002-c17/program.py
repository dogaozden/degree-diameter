"""Multi-base voltage lifts over non-abelian groups for the bipartite degree-diameter problem (numpy + lib only).

CONSTRUCTION.  Take a base bipartite multigraph with r A-vertices and r B-vertices.  Block (i, j) carries c_ij
darts, with row and column sums equal to d (circulant pattern: diagonal a, off-diagonal (d-a)/(r-1)).  Each dart
has a voltage v in a finite group G, and the voltages inside one block are pairwise distinct.  The lift has
vertices (A_i, g) and (B_j, g) for g in G, and dart (i, j, v) gives the edges (A_i, g) ~ (B_j, g*v).  The result is
bipartite, d-regular, simple, and has 2*r*|G| vertices.

DIAMETER.  Left multiplication by h in G is an automorphism, so every vertex of one base class looks alike.  The
diameter is at most D iff each of the 2r base vertices reaches every lift vertex within D steps.  The cost is the
number of unreached (base vertex, lift vertex) pairs; cost 0 means valid.  Each cost evaluation is one vectorised
reachability sweep, and a voltage move rewrites only the two neighbour columns of the changed dart.

SEARCH.  Simulated annealing on the voltages, round-robin over several (r, group) candidates chosen so that the
order 2*r*|G| exceeds the record 4000.  Every candidate that reaches cost 0 is verified with lib.is_valid.  The
largest verified lift is returned.  If none is found, a verified Haar graph of order 3582 is returned, and for
any other case a small always-valid graph.
"""
import itertools
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def _table_from_coords(elems, mulfun):
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)."""
    N, c = elems.shape
    base = int(elems.max()) + 1
    wts = base ** np.arange(c, dtype=np.int64)
    codes = elems.astype(np.int64) @ wts
    order = np.argsort(codes)
    sorted_codes = codes[order]
    MT = np.empty((N, N), dtype=np.int32)
    for i in range(N):
        prod = mulfun(elems[i][None, :], elems)
        MT[i] = order[np.searchsorted(sorted_codes, prod.astype(np.int64) @ wts)]
    return _finish(MT)


def group_heis(p):
    """Heisenberg group mod p, order p^3: (a,b,c)(a',b',c') = (a+a', b+b', c+c'+a*b')."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, matrices (a, b, c, d), order p(p^2-1)."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def make_group(spec):
    """Build a group table from a spec tuple."""
    kind = spec[0]
    if kind == 'meta':
        _, m, k = spec
        lam = next(l for l in range(2, m) if pow(l, k, m) == 1)
        return group_meta(m, k, lam)
    if kind == 'heisc':
        _, p, k = spec
        return group_times_cyclic(group_heis(p), k)
    if kind == 'sl2c':
        _, p, k = spec
        return group_times_cyclic(group_sl2(p), k)
    raise ValueError(kind)


# ------------------------------------------------------------------------------- lift evaluation

def _lift_cost(nbr, r, N, D):
    """Number of unreached (base vertex, lift vertex) pairs within D steps (0 = diameter <= D)."""
    S = 2 * r
    n = nbr.shape[0]
    reach = np.zeros((S, n), dtype=bool)
    idx = np.arange(S)
    reach[idx, idx * N] = True
    for _ in range(D):
        reach = reach | reach[:, nbr].any(axis=2)
    return S * n - int(np.count_nonzero(reach))


def _edges(nbr, r, N):
    """Edge list of the lift (every edge is listed once, from its A-side end)."""
    d = nbr.shape[1]
    xs = np.repeat(np.arange(r * N, dtype=np.int64), d)
    ys = nbr[:r * N].ravel()
    return 2 * r * N, list(zip(xs.tolist(), ys.tolist()))


class LiftSearch:
    """Simulated annealing over the dart voltages of one (r, group) candidate."""

    def __init__(self, r, d, D, MT, inv, rng):
        self.r, self.d, self.D = r, d, D
        self.MT, self.inv = MT, inv
        self.N = MT.shape[0]
        self.rng = rng
        self.g = np.arange(self.N)
        self.T = 0.5
        self.patience = 1500
        self.done = False
        self.solution = None
        self.restart()

    def _set(self, i, j, s, v):
        """Write voltage v on dart (i, j, s) and update the two affected neighbour columns."""
        r, N = self.r, self.N
        key = (i, j, s)
        self.volt[key] = v
        g = self.g
        self.nbr[i * N + g, self.colA[key]] = (r + j) * N + self.MT[g, v]
        self.nbr[(r + j) * N + g, self.colB[key]] = i * N + self.MT[g, self.inv[v]]

    def restart(self):
        rng, r, d, N = self.rng, self.r, self.d, self.N
        opts = [a for a in range(2, d - 1) if (d - a) % (r - 1) == 0]
        a = opts[int(rng.integers(len(opts)))]
        c = [[a if i == j else (d - a) // (r - 1) for j in range(r)] for i in range(r)]
        self.c = c
        self.colA, self.colB, self.darts = {}, {}, []
        for i in range(r):
            oa = 0
            for j in range(r):
                for s in range(c[i][j]):
                    self.colA[(i, j, s)] = oa + s
                    self.darts.append((i, j, s))
                oa += c[i][j]
        for j in range(r):
            ob = 0
            for i in range(r):
                for s in range(c[i][j]):
                    self.colB[(i, j, s)] = ob + s
                ob += c[i][j]
        self.volt = {}
        self.nbr = np.empty((2 * r * N, d), dtype=np.int64)
        for i in range(r):
            for j in range(r):
                vals = rng.choice(N, size=c[i][j], replace=False)
                for s in range(c[i][j]):
                    self._set(i, j, s, int(vals[s]))
        self.cur = _lift_cost(self.nbr, r, N, self.D)
        self.since = 0
        if self.cur == 0:
            self._record()

    def _record(self):
        self.done = True
        self.solution = self.nbr.copy()

    def edges(self):
        return _edges(self.solution, self.r, self.N)

    def run(self, t_end):
        rng = self.rng
        while not self.done and time.monotonic() < t_end:
            key = self.darts[int(rng.integers(len(self.darts)))]
            i, j, s = key
            block = {self.volt[(i, j, t)] for t in range(self.c[i][j])}
            v = int(rng.integers(self.N))
            if v in block:
                continue
            old = self.volt[key]
            old_cur = self.cur
            self._set(i, j, s, v)
            new = _lift_cost(self.nbr, self.r, self.N, self.D)
            delta = new - self.cur
            if delta <= 0 or rng.random() < math.exp(-delta / self.T):
                self.cur = new
                if new == 0:
                    self._record()
                    return
            else:
                self._set(i, j, s, old)
            if self.cur < old_cur:
                self.since = 0
            else:
                self.since += 1
            if self.since > self.patience:
                self.restart()
                if self.done:
                    return


# ------------------------------------------------------------------------------- candidate search

# (r, group spec).  Order 2*r*|G| must exceed 4000 to beat the record.
SPECS = [
    (2, ('meta', 101, 10)),     # 4040
    (2, ('meta', 79, 13)),      # 4108
    (2, ('heisc', 7, 3)),       # 4116
    (2, ('meta', 211, 5)),      # 4220
    (3, ('meta', 71, 10)),      # 4260
    (2, ('sl2c', 5, 9)),        # 4320
    (2, ('meta', 47, 23)),      # 4324
    (3, ('meta', 67, 11)),      # 4422
    (3, ('meta', 127, 6)),      # 4572
]

SLICE = 0.8


def lift_search(d, D, seed, end):
    """Round-robin the candidates until `end`.  Returns the largest verified valid lift as (n, edges), or None."""
    active = []
    for idx, (r, spec) in enumerate(SPECS):
        try:
            MT, inv = make_group(spec)
            rng = np.random.default_rng((seed * 1009 + idx) % (2 ** 32))
            active.append(LiftSearch(r, d, D, MT, inv, rng))
        except Exception:
            continue
    found = []
    while active and time.monotonic() < end:
        for c in list(active):
            now = time.monotonic()
            if now >= end:
                break
            try:
                c.run(min(end, now + SLICE))
            except Exception:
                active.remove(c)
                continue
            if c.done:
                active.remove(c)
                try:
                    n, edges = c.edges()
                    if lib.is_valid(n, edges, d, D):
                        found.append((n, edges))
                except Exception:
                    pass
    if not found:
        return None
    return max(found, key=lambda t: t[0])


# --------------------------------------------------------------------------- fallback and helpers

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid (checked with lib.is_valid)."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


TARGET = (10, 5)

# Valid Haar graph of order 3582 (checked at run time); used only if no lift is found.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    end = time.monotonic() + 0.72 * time_limit
    try:
        res = lift_search(d, D, seed, end)
    except Exception:
        res = None
    if res is not None:
        return res
    try:
        MT, inv = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)
