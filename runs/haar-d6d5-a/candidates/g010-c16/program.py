"""Multi-class voltage lifts for the bipartite degree-diameter problem (target d=6, D=5).

Construction: a base bipartite multigraph with a A-classes and a B-classes. Class A_i and class B_j are joined by
c_ij darts, with row and column sums equal to d. Each dart carries a voltage g in a finite group G of order N, and
(A_i, x) ~ (B_j, x*g). The lift has 2aN vertices and is bipartite and d-regular. With a = 1 it is the Haar graph.

Left multiplication by any h in G is an automorphism, so the diameter is at most D iff a BFS of depth D from the
identity of every class reaches all of the graph. The cost counts unreached (source, vertex) pairs, computed for all
2a sources at once. Simulated annealing moves one voltage at a time. Any lift that reaches cost 0 is checked with
lib.is_valid before it is returned. A valid smaller Haar graph is the fallback.
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
    """Z_m x|_lam Z_k with (a, j) -> a*k + j and (a, j)(b, l) = (a + lam^j b, j + l). Needs lam^k = 1 mod m."""
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
    """Table of a group given by an (N, c) coordinate array (element 0 = identity) and a vectorised product."""
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
    """Heisenberg group mod p, order p^3, identity (0,0,0) first."""
    e = np.array(list(itertools.product(range(p), repeat=3)), dtype=np.int64)

    def mul(X, Y):
        return np.stack([(X[..., 0] + Y[..., 0]) % p, (X[..., 1] + Y[..., 1]) % p,
                         (X[..., 2] + Y[..., 2] + X[..., 0] * Y[..., 1]) % p], axis=-1)
    return _table_from_coords(e, mul)


def group_agl(q, k=None):
    """GF(q) x| C_k (default k = q-1, i.e. AGL(1, q)), with (b1, a1)(b2, a2) = (b1 + a1 b2, a1 a2)."""
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


def metacyclic_candidates(lo, hi, limit):
    """Non-abelian metacyclic Z_m x|_lam Z_k with lo <= m*k <= hi, smallest order first."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((f"Z_{m} x| Z_{k} (lam={lam}), order {N}", N, m, k, lam))
                    break
            if len(out) >= limit:
                return out
    return out


# ------------------------------------------------------------------------------------ lift cost

def lift_cost(MT, inv, a, D, darts):
    """Uncovered (source, vertex) pairs after a depth-D BFS from the identity of every class (0 = diameter <= D).

    Classes 0..a-1 are A-classes and a..2a-1 are B-classes. Dart (i, j, g) gives arcs A_i -> B_j (x -> x*g) and
    B_j -> A_i (x -> x*g^-1). Left multiplication is an automorphism, so one source per class suffices.
    """
    N = MT.shape[0]
    C = 2 * a
    R = np.zeros((C, C, N), dtype=bool)
    for s in range(C):
        R[s, s, 0] = True
    arcs = []
    for i, j, g in darts:
        arcs.append((i, a + j, MT[:, g]))
        arcs.append((a + j, i, MT[:, inv[g]]))
    F = R.copy()
    for _ in range(D):
        new = np.zeros_like(R)
        for c, c2, p in arcs:
            new[:, c2, p] |= F[:, c, :]
        new &= ~R
        if not new.any():
            break
        R |= new
        F = new
    return C * C * N - int(R.sum())


def lift_graph(MT, a, darts):
    """Build the lift: vertex id = class * N + x; returns (n, edges)."""
    N = MT.shape[0]
    xs = np.arange(N)
    edges = []
    for i, j, g in darts:
        us = i * N + xs
        vs = (a + j) * N + MT[:, g]
        edges.extend(zip(us.tolist(), vs.tolist()))
    return 2 * a * N, edges


def random_darts(N, a, cmat, rng):
    darts = []
    for i in range(a):
        for j in range(a):
            c = cmat[i][j]
            if c:
                for g in rng.choice(N, c, replace=False):
                    darts.append([i, j, int(g)])
    return darts


# ---------------------------------------------------------------------------------------- search

PATIENCE = 2500


class LiftSearch:
    """Simulated annealing over the voltages of one (group, base-multigraph) pair, resumable across slices."""

    def __init__(self, MT, inv, a, D, cmat, rng):
        self.MT, self.inv, self.a, self.D, self.cmat = MT, inv, a, D, cmat
        self.N = MT.shape[0]
        self.rng = rng
        self.darts = None
        self.cur = None
        self.best = None
        self.bestc = 10 ** 9
        self.since = 0
        self.T = 1.0

    def _cost(self):
        return lift_cost(self.MT, self.inv, self.a, self.D, self.darts)

    def _restart(self):
        self.darts = random_darts(self.N, self.a, self.cmat, self.rng)
        self.cur = self._cost()
        self.since = 0
        self.T = float(self.rng.uniform(0.6, 2.5))
        self._note()

    def _note(self):
        if self.cur < self.bestc:
            self.bestc = self.cur
            self.best = [list(x) for x in self.darts]

    def run(self, deadline):
        """Anneal until deadline. Returns True once a cost-0 lift is found."""
        if self.darts is None:
            self._restart()
        while time.monotonic() < deadline and self.bestc > 0:
            e = int(self.rng.integers(len(self.darts)))
            i, j, g_old = self.darts[e]
            used = {x[2] for x in self.darts if x[0] == i and x[1] == j}
            ng = int(self.rng.integers(self.N))
            if ng in used:
                continue
            self.darts[e][2] = ng
            c = self._cost()
            delta = c - self.cur
            if delta <= 0 or self.rng.random() < math.exp(-delta / self.T):
                if delta < 0:
                    self.since = 0
                self.cur = c
                self._note()
            else:
                self.darts[e][2] = g_old
            self.since += 1
            if self.since > PATIENCE:
                self._restart()
        return self.bestc == 0

    def graph(self, d, D):
        """Checked graph for the best darts, or None."""
        n, edges = lift_graph(self.MT, self.a, self.best)
        return (n, edges) if lib.is_valid(n, edges, d, D) else None


# ------------------------------------------------------------------------------------ plan / glue

TARGET = (6, 5)

C2 = [[[3, 3], [3, 3]], [[2, 4], [4, 2]]]                    # a = 2, row and column sums 6
C3 = [[[2, 2, 2], [2, 2, 2], [2, 2, 2]],
      [[1, 2, 3], [2, 3, 1], [3, 1, 2]]]                     # a = 3, row and column sums 6
C1 = [[[6]]]                                                 # a = 1, the Haar graph

PLAN = []
for _name, _N, _m, _k, _lam in metacyclic_candidates(172, 186, 3):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 2, C2[0]))
for _name, _N, _m, _k, _lam in metacyclic_candidates(172, 186, 2):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 2, C2[1]))
PLAN.append(("Heis(5), order 125", lambda: group_heis(5), 3, C3[0]))
PLAN.append(("Heis(5), order 125 (c2)", lambda: group_heis(5), 3, C3[1]))
for _name, _N, _m, _k, _lam in metacyclic_candidates(115, 130, 2):
    PLAN.append((_name, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 3, C3[1]))
PLAN.append(("AGL(1,13), order 156", lambda: group_agl(13), 3, C3[0]))
PLAN.append(("AGL(1,13) x Z_2, order 312", lambda: group_times_cyclic(group_agl(13), 2), 2, C2[0]))
PLAN.append(("Heis(7), order 343 (Haar)", lambda: group_heis(7), 1, C1[0]))
PLAN.append(("Heis(3) x Z_13, order 351 (Haar)", lambda: group_times_cyclic(group_heis(3), 13), 1, C1[0]))
for _name, _N, _m, _k, _lam in metacyclic_candidates(343, 372, 2):
    PLAN.append((_name + " (Haar)", (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam)), 1, C1[0]))


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def run(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline_all = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)

    states = []
    for name, builder, a, cmat in PLAN:
        if time.monotonic() > t0 + 0.30 * time_limit:
            break
        try:
            MT, inv = builder()
        except Exception:
            continue
        states.append(LiftSearch(MT, inv, a, D, cmat, rng))

    slice_t = 0.25
    while states and time.monotonic() < deadline_all:
        for st in states:
            now = time.monotonic()
            if now >= deadline_all:
                break
            try:
                done = st.run(min(deadline_all, now + slice_t))
            except Exception:
                continue
            if done:
                try:
                    g = st.graph(d, D)
                except Exception:
                    g = None
                if g is not None:
                    return g
                st.bestc = 10 ** 9     # verification failed: keep searching this state
        slice_t *= 1.6

    # Safe fallback: a valid smaller Haar graph (order 660).
    try:
        MT, _ = group_meta(33, 10, 26)
        n, edges = lift_graph(MT, 1, [[0, 0, g] for g in [0, 179, 116, 180, 47, 306]])
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    return trivial(d, D)


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    return run(d, D, seed, time_limit)
