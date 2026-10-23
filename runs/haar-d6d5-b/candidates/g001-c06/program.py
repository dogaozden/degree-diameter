"""Bold variant for d=6, D=5: multi-orbit lifts instead of single Haar graphs.

Construction.  Take a finite group G (order N), a k x k matrix M of nonnegative integers with all row and
column sums d, and a connection element s for each of the sum(M) "darts".  Vertices are k copies of G on the
A side and k copies on the B side (2kN vertices).  A dart in block (i, j) with element s joins
(g, A_i) to (s*g, B_j).  Every row and column has exactly d darts, so the graph is bipartite and d-regular.
Right multiplication by G is an automorphism, so the diameter is at most D iff a BFS from each of the 2k
base vertices (e, x) reaches every vertex within D steps.  That gives an exact cost (count of unreached
pairs), so no proxy is needed.

Search.  Simulated annealing over the dart elements, with best-of-K candidate moves, per-group chains run
round-robin so no single group consumes the whole budget.  Any cost-0 state is rebuilt and checked with
lib.is_valid before it is returned.  The 660-vertex Haar graph from the parent is kept as a fallback, and
the trivial graph is the last resort.
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
    """Table of a group given as an (N, c) integer coordinate array (element 0 must be the identity)
    and a vectorised product mulfun(X, Y) of two (..., c) arrays."""
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
    """Heisenberg group mod p, order p^3, identity first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_sl2(p):
    """SL(2, p) for a prime p, order p(p^2-1), identity first."""
    allm = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    allm = allm[(allm[:, 0] * allm[:, 3] - allm[:, 1] * allm[:, 2]) % p == 1]
    ident = np.nonzero((allm == np.array([1, 0, 0, 1])).all(axis=1))[0][0]
    allm = np.vstack([allm[ident:ident + 1], np.delete(allm, ident, axis=0)])

    def mul(X, Y):
        a, b, c, d = (X[..., i] for i in range(4))
        e, f, g, h = (Y[..., i] for i in range(4))
        return np.stack([(a * e + b * g) % p, (a * f + b * h) % p, (c * e + d * g) % p, (c * f + d * h) % p], axis=-1)
    return _table_from_coords(allm, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default k = q-1, AGL(1, q)), identity first."""
    F = lib.GF(q)
    k = q - 1 if k is None else k
    H = [a for a in range(1, q) if F.pow(a, k) == 1]
    assert len(H) == k
    e = np.array([(0, 1)] + [(b, a) for b in range(q) for a in H if (b, a) != (0, 1)], dtype=np.int64)
    add, mulT = F.add_table, F.mul_table

    def mul(X, Y):
        return np.stack([add[X[..., 0], mulT[X[..., 1], Y[..., 0]]], mulT[X[..., 1], Y[..., 1]]], axis=-1)
    return _table_from_coords(e, mul)


def group_times_cyclic(grp, k):
    """Direct product of a table group (MT, inv) with Z_k; element (g, c) has index g*k + c."""
    MT0, _ = grp
    n0 = MT0.shape[0]
    c = np.arange(k, dtype=np.int64)
    MT = np.empty((n0 * k, n0 * k), dtype=np.int32)
    for g in range(n0):
        MT[g * k:(g + 1) * k] = (MT0[g][None, :, None] * k + (c[:, None, None] + c[None, None, :]) % k).reshape(k, n0 * k)
    return _finish(MT)


def _meta_cands(lo, hi, limit):
    """Some (m, k, lam) with m*k in [lo, hi], lam != 1 (non-abelian), lam^k = 1 mod m."""
    out = []
    for N in range(lo, hi + 1):
        for kk in range(2, N + 1):
            if N % kk:
                continue
            m = N // kk
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, kk, m) == 1 % m:
                    out.append((m, kk, lam))
                    break
    return out[:limit]


# ----------------------------------------------------------------------------------------- the lift

D_TARGET = 5
SLICE = 1.0       # seconds per chain per round-robin round
K_CAND = 4        # candidate moves per step
TEMP = 1.0
PATIENCE = 1500


def block_darts(M):
    """Darts of a block matrix M: list of (i, j) per dart, plus per-dart slot index within its row and column."""
    k = len(M)
    darts = []
    for i in range(k):
        for j in range(k):
            darts += [(i, j)] * M[i][j]
    rowc, colc, slotA, slotB = [0] * k, [0] * k, [], []
    for i, j in darts:
        slotA.append(rowc[i])
        rowc[i] += 1
        slotB.append(colc[j])
        colc[j] += 1
    return darts, slotA, slotB


class Lift:
    """Annealing state for one (group, block matrix) pair."""

    def __init__(self, MT, inv, M, d, D, rng):
        self.MT, self.inv = MT, inv
        self.N = MT.shape[0]
        self.k = len(M)
        self.d = d
        self.D = D
        self.rng = rng
        self.darts, self.slotA, self.slotB = block_darts(M)
        self.T = len(self.darts)
        self.V = 2 * self.k * self.N
        self.mates = [[u for u in range(self.T) if self.darts[u] == self.darts[t]] for t in range(self.T)]
        self.S = self.random_state()
        self.cur = self.cost(self.S)
        self.best = self.cur
        self.bestS = list(self.S)
        self.since = 0

    def random_state(self):
        S = [0] * self.T
        for blk in set(self.darts):
            idx = [t for t in range(self.T) if self.darts[t] == blk]
            vals = self.rng.choice(self.N, size=len(idx), replace=False)
            for t, v in zip(idx, vals):
                S[t] = int(v)
        return S

    def distinct(self, S):
        for t in range(self.T):
            for u in self.mates[t]:
                if u != t and S[u] == S[t]:
                    return False
        return True

    def neighbours(self, S):
        N, k, MT, inv = self.N, self.k, self.MT, self.inv
        nb = np.empty((self.V, self.d), dtype=np.int64)
        for t, (i, j) in enumerate(self.darts):
            s = S[t]
            nb[i * N:(i + 1) * N, self.slotA[t]] = (k + j) * N + MT[s]
            nb[(k + j) * N:(k + j + 1) * N, self.slotB[t]] = i * N + MT[inv[s]]
        return nb

    def cost(self, S):
        """Number of (source, vertex) pairs at distance > D, over the 2k base sources."""
        nb = self.neighbours(S)
        k2 = 2 * self.k
        R = np.zeros((k2, self.V), dtype=bool)
        R[np.arange(k2), np.arange(k2) * self.N] = True
        for _ in range(self.D):
            new = R.copy()
            for slot in range(self.d):
                new |= R[:, nb[:, slot]]
            R = new
        return int(k2 * self.V - np.count_nonzero(R))

    def run(self, until):
        """Anneal until the monotonic time `until`.  Returns True once a cost-0 state is known."""
        rng = self.rng
        S = self.S
        while time.monotonic() < until:
            if self.best == 0:
                break
            t = int(rng.integers(self.T))
            orig = S[t]
            forb = {S[u] for u in self.mates[t] if u != t}
            cands = []
            for _ in range(K_CAND):
                x = int(rng.integers(self.N))
                if x in forb or x == orig or x in cands:
                    continue
                cands.append(x)
            if cands:
                costs = []
                for x in cands:
                    S[t] = x
                    costs.append(self.cost(S))
                S[t] = orig
                j = int(np.argmin(np.array(costs, dtype=float) + rng.random(len(costs)) * 0.5))
                delta = costs[j] - self.cur
                if delta <= 0 or rng.random() < math.exp(-delta / TEMP):
                    S[t] = cands[j]
                    self.cur = costs[j]
                if self.cur < self.best:
                    self.best = self.cur
                    self.bestS = list(S)
                    self.since = 0
                    continue
            self.since += 1
            if self.since > PATIENCE:
                if rng.random() < 0.5:
                    S = list(self.bestS)
                    for t2 in rng.choice(self.T, 2, replace=False):
                        S[int(t2)] = int(rng.integers(self.N))
                    if not self.distinct(S):
                        S = self.random_state()
                else:
                    S = self.random_state()
                self.S = S
                self.cur = self.cost(S)
                self.since = 0
                if self.cur < self.best:
                    self.best = self.cur
                    self.bestS = list(S)
        self.S = S
        return self.best == 0

    def edges(self, S):
        N, k = self.N, self.k
        out = []
        for t, (i, j) in enumerate(self.darts):
            col = self.MT[S[t]]
            for g in range(N):
                out.append((i * N + g, (k + j) * N + int(col[g])))
        return 2 * k * N, out


# ----------------------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])   # valid Haar graph, 660 vertices


def fallback(d, D):
    try:
        MT, _ = FALLBACK[0]()
        g = checked(MT, FALLBACK[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# ----------------------------------------------------------------------------------------- plan

M2A = [[3, 3], [3, 3]]                      # k = 2, 12 darts, 4|G| vertices
M3A = [[2, 2, 2], [2, 2, 2], [2, 2, 2]]     # k = 3, 18 darts, 6|G| vertices
M3B = [[3, 2, 1], [2, 2, 2], [1, 2, 3]]


def build_plan():
    plan = []
    for m, kk, lam in _meta_cands(172, 200, 3):
        plan.append((f"Z{m}x|Z{kk}", lambda m=m, kk=kk, lam=lam: group_meta(m, kk, lam), M2A))
    plan.append(("Heis3xZ7", lambda: group_times_cyclic(group_heis(3), 7), M2A))
    plan.append(("AGL(1,9)xZ3", lambda: group_times_cyclic(group_agl(9), 3), M2A))
    plan.append(("AGL(1,16)", lambda: group_agl(16), M2A))
    plan.append(("SL(2,5)xk3", lambda: group_sl2(5), M3A))
    plan.append(("SL(2,5)xk3 B", lambda: group_sl2(5), M3B))
    plan.append(("Heis5 k3", lambda: group_heis(5), M3A))
    return plan


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    end_all = t0 + 0.75 * time_limit
    rng = np.random.default_rng(seed)
    chains = []
    for name, builder, M in build_plan():
        if time.monotonic() > end_all - 2.0:
            break
        try:
            MT, inv = builder()
            if MT.shape[0] * 2 * len(M) <= 684:
                continue
            chains.append([name, Lift(MT, inv, M, d, D, rng), True])
        except Exception:
            continue
    while time.monotonic() < end_all and any(c[2] for c in chains):
        for c in chains:
            if not c[2]:
                continue
            now = time.monotonic()
            if now >= end_all:
                break
            ch = c[1]
            if ch.run(min(end_all, now + SLICE)):
                try:
                    n, edges = ch.edges(ch.bestS)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
                except Exception:
                    pass
                c[2] = False   # claimed cost 0 but not valid: retire this chain
    return fallback(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != (6, D_TARGET):
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit)
    except Exception:
        return fallback(d, D)
