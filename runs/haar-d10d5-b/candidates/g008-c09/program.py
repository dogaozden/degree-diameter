"""Bold variant for d=10, D=5: voltage lifts over multi-vertex circulant bases, with the parent's Haar fallback.

CONSTRUCTION.  Take a finite group G of order N (metacyclic Z_m x| Z_k) and a base bipartite multigraph with
s A-vertices and s B-vertices, arranged circulantly: A_i joins B_{(i+k) mod s} with multiplicity c_k, where
(c_0..c_{s-1}) sums to d = 10.  Each dart e carries a voltage g_e in G, and the lift has edges
(A_i, x) ~ (B_j, x*g_e) for every dart e = (i, j).  The lift is simple (parallel darts get distinct voltages),
10-regular, bipartite, and has 2sN vertices.  Left multiplication by any h in G is an automorphism, so the
diameter is at most 5 iff a BFS of depth 5 from each of the 2s base representatives (u, e) reaches every vertex.
The annealing cost is the total number of unreached vertices over those representatives, plus a penalty for
repeated voltages on parallel darts.  Each step is cheap (numpy BFS), so many more candidates fit in the budget
than with full pair-coverage counting.

Configurations satisfy 2sN > 3582, so any valid lift beats the fallback.  Candidates are annealed round-robin,
each keeping its state.  The first one that passes lib.is_valid is returned.  If none passes, the parent's valid
Haar graph (3582 vertices) is returned, and the trivial graph is the last resort.
"""
import math
import time
from math import gcd

import numpy as np

import lib


TARGET = (10, 5)
DEG = 10
D_T = 5
PATIENCE = 1500
CHUNK = 40
TEMP = 2.0

FALLBACK_MOD = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

# Compositions of 10 into s parts: c_k = multiplicity of the dart from A_i to B_{i+k}.
COMPS = {
    2: [(1, 9), (2, 8), (3, 7), (4, 6), (5, 5)],
    3: [(4, 3, 3), (3, 4, 3), (5, 3, 2), (4, 4, 2), (6, 2, 2)],
    4: [(3, 3, 2, 2), (4, 2, 2, 2), (3, 3, 3, 1), (4, 3, 2, 1)],
    5: [(2, 2, 2, 2, 2), (3, 2, 2, 2, 1), (4, 2, 2, 1, 1), (3, 3, 2, 1, 1)],
}
# Vertex-count ranges: smallest N with 2*s*N > 3582, up to a generous cap.
RANGES = {2: (896, 1000), 3: (598, 760), 4: (448, 570), 5: (359, 460)}


# ----------------------------------------------------------------------------- shared helpers

def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


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


def _meta_params(lo, hi):
    """Map N -> (m, k, lam) for a nonabelian metacyclic group of order N in [lo, hi] (first found)."""
    out = {}
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            lam = next((l for l in range(2, m) if gcd(l, m) == 1 and pow(l, k, m) == 1), None)
            if lam is not None:
                out[N] = (m, k, lam)
                break
    return out


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


# ----------------------------------------------------------------------------- lift search

class _Lift:
    """Voltage assignment on a circulant base lifted over a group table (MT, inv) of order N."""

    def __init__(self, s, comp, N, MT, inv, rng):
        self.s, self.N = s, N
        self.MT, self.inv = MT, inv
        darts = []
        for i in range(s):
            for k, c in enumerate(comp):
                for _ in range(c):
                    darts.append((i, (i + k) % s))
        self.darts = darts
        E = len(darts)
        self.E = E
        cntA = [0] * s
        cntB = [0] * s
        self.sA = [0] * E
        self.sB = [0] * E
        for e, (i, j) in enumerate(darts):
            self.sA[e] = cntA[i]
            cntA[i] += 1
            self.sB[e] = cntB[j]
            cntB[j] += 1
        self.pairs = [(e, f) for e in range(E) for f in range(e + 1, E) if darts[e] == darts[f]]
        self.xs = np.arange(N)
        self.n = 2 * s * N
        self.rng = rng
        self.volt = rng.integers(0, N, size=E).astype(np.int64)
        self.cur = self.cost()
        self.best = self.cur
        self.since = 0

    def adjacency(self):
        s, N = self.s, self.N
        adj = np.empty((self.n, DEG), dtype=np.int64)
        for e, (i, j) in enumerate(self.darts):
            g = int(self.volt[e])
            adj[i * N:(i + 1) * N, self.sA[e]] = (s + j) * N + self.MT[self.xs, g]
            adj[(s + j) * N:(s + j + 1) * N, self.sB[e]] = i * N + self.MT[self.xs, int(self.inv[g])]
        return adj

    def cost(self):
        adj = self.adjacency()
        n = self.n
        total = 0
        for u in range(2 * self.s):
            r = u * self.N
            seen = np.zeros(n, dtype=bool)
            seen[r] = True
            front = np.array([r], dtype=np.int64)
            for _ in range(D_T):
                nb = adj[front].ravel()
                nb = np.unique(nb[~seen[nb]])
                if nb.size == 0:
                    break
                seen[nb] = True
                front = nb
            total += n - int(seen.sum())
        pen = sum(1 for e, f in self.pairs if self.volt[e] == self.volt[f])
        return total + 1000 * pen

    def restart(self):
        self.volt = self.rng.integers(0, self.N, size=self.E).astype(np.int64)
        self.cur = self.cost()
        self.best = self.cur
        self.since = 0

    def step(self, temp):
        e = int(self.rng.integers(self.E))
        old = int(self.volt[e])
        new = int(self.rng.integers(self.N))
        if new == old:
            return
        self.volt[e] = new
        c = self.cost()
        delta = c - self.cur
        if delta <= 0 or self.rng.random() < math.exp(-delta / temp):
            self.cur = c
            if c < self.best:
                self.best = c
                self.since = 0
            else:
                self.since += 1
        else:
            self.volt[e] = old
            self.since += 1
        if self.since > PATIENCE:
            self.restart()

    def graph(self):
        adj = self.adjacency()
        nA = self.s * self.N
        a = np.repeat(np.arange(nA, dtype=np.int64), DEG).tolist()
        b = adj[:nA].ravel().tolist()
        return self.n, [(int(x), int(y)) for x, y in zip(a, b)]


def search_lifts(seed, deadline):
    """Round-robin annealing over (base composition, group) configurations; returns a checked (n, edges) or None."""
    rng = np.random.default_rng(seed)
    params = _meta_params(340, 1100)
    configs = []
    for s, (lo, hi) in RANGES.items():
        avail = [N for N in range(lo, hi + 1) if N in params]
        if not avail:
            continue
        idx = sorted({int(round(x)) for x in np.linspace(0, len(avail) - 1, min(4, len(avail)))})
        for N in [avail[i] for i in idx]:
            for comp in COMPS[s]:
                configs.append((s, comp, N))
    if not configs:
        return None
    order = rng.permutation(len(configs))
    configs = [configs[i] for i in order]
    states = [None] * len(configs)
    alive = [True] * len(configs)
    mt_cache = {}

    while time.monotonic() < deadline:
        any_alive = False
        for ci, (s, comp, N) in enumerate(configs):
            if time.monotonic() >= deadline:
                return None
            if not alive[ci]:
                continue
            any_alive = True
            if states[ci] is None:
                if N not in mt_cache:
                    m, k, lam = params[N]
                    mt_cache[N] = group_meta(m, k, lam)
                MT, inv = mt_cache[N]
                states[ci] = _Lift(s, comp, N, MT, inv, rng)
            st = states[ci]
            for _ in range(CHUNK):
                if st.cur == 0:
                    break
                st.step(TEMP)
            if st.cur == 0:
                n, edges = st.graph()
                if lib.is_valid(n, edges, DEG, D_T):
                    return n, edges
                alive[ci] = False  # should not happen; drop this configuration
        if not any_alive:
            break
    return None


# ----------------------------------------------------------------------------- fallback

def fallback_graph(d, D):
    """The parent's valid 3582-vertex Haar graph, checked at run time."""
    MT, _ = group_meta(*FALLBACK_MOD)
    n, edges = haar_edges(MT, FALLBACK_S)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


# ----------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    deadline = t0 + max(2.0, 0.8 * time_limit - 3.0)
    try:
        res = search_lifts(seed, deadline)
        if res is not None:
            return res
    except Exception:
        pass
    try:
        res = fallback_graph(d, D)
        if res is not None:
            return res
    except Exception:
        pass
    return trivial(d, D)
