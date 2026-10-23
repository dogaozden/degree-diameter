"""Bi-Cayley search for the bipartite degree-diameter problem at diameter 5 (numpy only).

THEORY.  Let G be a finite group.  Take four orbits: A_0, A_1 (one side) and B_0, B_1 (other side), each a
copy of G.  For each pair (i, j) choose a set S_ij of k_ij group elements, with k_00 = k_11 = a and
k_01 = k_10 = d - a.  Edges are (g, A_i) ~ (g*s, B_j) for s in S_ij.  Each A_i vertex has degree
k_i0 + k_i1 = d and each B_j vertex has degree k_0j + k_1j = d, so the graph is bipartite and d-regular on
4|G| vertices.

Left multiplication by any h in G is an automorphism, so each orbit is vertex-transitive.  Hence the diameter
is at most D iff every vertex lies within distance D of one representative per orbit (4 BFS runs).  The cost
is the number of vertices left unreached by those four BFS runs; cost 0 means a valid graph.

WHAT THIS FILE DOES.  Samples non-abelian metacyclic groups with orders near 172 (so 4|G| beats 684),
anneals the block sets to cost 0 using the BFS cost, round-robins over the candidate groups with growing
time slices, and verifies the result with lib.is_valid.  If nothing succeeds, it falls back to a valid
smaller Haar graph, and then to an always-valid trivial graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (6, 5)


# ----------------------------------------------------------------------------------------- group tables

def _finish(MT):
    """Return (MT, inverse array) for a table whose identity is element 0."""
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k with (a, j) -> index a*k + j and (a, j)(b, l) = (a + lam^j b, j + l)."""
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = (((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k
                     + (j[lo:hi, None] + j[None, :]) % k)
    return _finish(MT)


def metacyclic_candidates(lo, hi, per_pair, limit):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with lo <= m*k <= hi."""
    out = []
    for N in range(lo, hi + 1):
        for k in range(2, N):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    out.append((N, m, k, lam))
                    cnt += 1
                    if cnt >= per_pair:
                        break
            if len(out) >= limit:
                return out
    return out


# ------------------------------------------------------------------------------------ bi-Cayley graph

def build_adj(MT, inv, blocks, N, d):
    """Adjacency array (4N x d) of the bi-Cayley graph.
    Orbits: A_0 = [0, N), A_1 = [N, 2N), B_0 = [2N, 3N), B_1 = [3N, 4N)."""
    ar = np.arange(N, dtype=np.int64)
    adj = np.empty((4 * N, d), dtype=np.int64)
    for i in range(2):
        cols = []
        for j in range(2):
            for s in blocks[i][j]:
                cols.append(2 * N + j * N + MT[ar, s].astype(np.int64))
        adj[i * N:(i + 1) * N] = np.column_stack(cols)
    for j in range(2):
        cols = []
        for i in range(2):
            for s in blocks[i][j]:
                cols.append(i * N + MT[ar, inv[s]].astype(np.int64))
        adj[2 * N + j * N:2 * N + (j + 1) * N] = np.column_stack(cols)
    return adj


def _reach(adj, src, D):
    """Number of vertices within distance D of src."""
    n = adj.shape[0]
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    frontier = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = adj[frontier].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        frontier = nb
    return int(seen.sum())


def cost_of(MT, inv, blocks, N, d, D):
    """Unreached vertices over the four orbit representatives (0 iff diameter <= D)."""
    adj = build_adj(MT, inv, blocks, N, d)
    n = 4 * N
    total = 0
    for src in (0, N, 2 * N, 3 * N):
        total += n - _reach(adj, src, D)
    return total


def build_graph(MT, N, blocks, d):
    """Edge list (n, edges) of the bi-Cayley graph."""
    edges = []
    for i in range(2):
        for j in range(2):
            for s in blocks[i][j]:
                s = int(s)
                for g in range(N):
                    edges.append((i * N + g, 2 * N + j * N + int(MT[g, s])))
    return 4 * N, edges


# ------------------------------------------------------------------------------------------ search

class BiCayleySearch:
    """Simulated annealing over the four connection blocks, resumable across time slices."""

    def __init__(self, MT, inv, N, d, D, rng, patience=6000):
        self.MT, self.inv, self.N, self.d, self.D = MT, inv, N, d, D
        self.rng = rng
        self.patience = patience
        self.best_c = None
        self.best = None
        self._restart()

    def _cost(self, blocks):
        return cost_of(self.MT, self.inv, blocks, self.N, self.d, self.D)

    def _restart(self):
        rng, N, d = self.rng, self.N, self.d
        a = int(rng.choice([2, 3, 4]))           # k_00 = k_11 = a, k_01 = k_10 = d - a
        self.K = [[a, d - a], [d - a, a]]
        self.temp = float(rng.choice([0.7, 1.2, 2.0]))
        self.blocks = [[rng.choice(N, size=self.K[i][j], replace=False).astype(np.int64)
                        for j in range(2)] for i in range(2)]
        self.cur = self._cost(self.blocks)
        self.since = 0
        self._note()

    def _note(self):
        if self.best_c is None or self.cur < self.best_c:
            self.best_c = self.cur
            self.best = [[b.copy() for b in row] for row in self.blocks]

    def step(self):
        if self.since > self.patience:
            self._restart()
            return
        rng, N = self.rng, self.N
        i = int(rng.integers(2))
        j = int(rng.integers(2))
        blk = self.blocks[i][j]
        t = int(rng.integers(blk.size))
        while True:
            x = int(rng.integers(N))
            if not np.any(blk == x):
                break
        new = blk.copy()
        new[t] = x
        trial = [list(row) for row in self.blocks]
        trial[i][j] = new
        c = self._cost(trial)
        delta = c - self.cur
        if delta <= 0 or rng.random() < math.exp(-delta / self.temp):
            self.blocks = trial
            self.cur = c
            if c < self.best_c:
                self._note()
                self.since = 0
                return
        self.since += 1

    def run(self, deadline):
        while time.monotonic() < deadline and self.best_c != 0:
            self.step()
        return self.best_c, self.best


# --------------------------------------------------------------------------------- Haar fallback

def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked_haar(MT, S, d, D):
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# ------------------------------------------------------------------------------------------- driver

def run(d, D, seed, time_limit, plan, fallback):
    """plan: list of (N, builder) where builder() returns (MT, inv).  Candidates are time-sliced
    round-robin with growing slices; each keeps its search state between slices."""
    t0 = time.monotonic()
    deadline = t0 + 0.80 * time_limit
    rng = np.random.default_rng(seed)
    states = {}
    dead = set()
    slice_len = 0.5
    while time.monotonic() < deadline - 0.05:
        for idx, (N, builder) in enumerate(plan):
            if idx in dead:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            if idx not in states:
                try:
                    MT, inv = builder()
                    states[idx] = BiCayleySearch(MT, inv, N, d, D, rng)
                except Exception:
                    dead.add(idx)
                    continue
            st = states[idx]
            end = min(deadline, now + slice_len)
            try:
                c, blocks = st.run(end)
            except Exception:
                dead.add(idx)
                continue
            if c == 0 and blocks is not None:
                try:
                    n, edges = build_graph(st.MT, st.N, blocks, d)
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
                except Exception:
                    pass
                dead.add(idx)
        slice_len = min(slice_len * 1.5, 6.0)

    try:
        MT, _ = fallback[0]()
        g = checked_haar(MT, fallback[1], d, D)
        if g is not None:
            return g
    except Exception:
        pass
    return trivial(d, D)


# Target plan: four-orbit bi-Cayley graphs over metacyclic groups of order 172..200 (4|G| > 684),
# then order 168..171 as a safety net.
PLAN = []
for _N, _m, _k, _lam in metacyclic_candidates(172, 200, 1, 8):
    PLAN.append((_N, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))
for _N, _m, _k, _lam in metacyclic_candidates(168, 171, 1, 2):
    PLAN.append((_N, (lambda m=_m, k=_k, lam=_lam: group_meta(m, k, lam))))

# Valid smaller Haar graph (order 330, 660 vertices), checked at run time.
FALLBACK = (lambda: group_meta(33, 10, 26), [0, 179, 116, 180, 47, 306])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    try:
        return run(d, D, seed, time_limit, PLAN, FALLBACK)
    except Exception:
        return trivial(d, D)
