"""Bold variant for d=10, D=5: multi-vertex voltage lifts over metacyclic groups.

A base multigraph with r vertices on each side (r in {2,3,4}) carries d darts per vertex, arranged as a sum of d
random permutation matrices, so every base vertex has degree d. Each dart (i, j, x) joins (A_i, g) to (B_j, x*g)
for a group element x. Right multiplication by h is an automorphism, so only the 2r fibre representatives (b, e)
need BFS to depth 5. Cost = number of vertices left unreached over those sources; cost 0 is a valid graph.
Annealing runs over the voltages in round-robin over several (group, r) candidates. The parent's Haar graph is
kept as a checked fallback, so every case still returns a valid graph.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
SEARCH_FRAC = 0.74
MAX_RUNS = 16
PATIENCE = 1500
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]   # Haar set on group_meta(199, 9, 180)


# ----------------------------------------------------------------------------- groups and small helpers

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int64)
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def group_meta(m, k, lam):
    """Z_m x|_lam Z_k, element (a, j) -> a*k + j, (a,j)(b,l) = (a + lam^j b, j + l).  Needs lam^k = 1 mod m."""
    assert pow(lam, k, m) == 1 % m
    pw = np.array([pow(lam, j, m) for j in range(k)], dtype=np.int64)
    N = m * k
    g = np.arange(N, dtype=np.int64)
    a, j = g // k, g % k
    MT = np.empty((N, N), dtype=np.int64)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((a[lo:hi, None] + pw[j[lo:hi], None] * a[None, :]) % m) * k + (j[lo:hi, None] + j[None, :]) % k
    return _finish(MT)


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def block_counts(r, d, rng):
    """r x r nonnegative integer matrix with all row and column sums d (sum of d random permutation matrices)."""
    M = np.zeros((r, r), dtype=np.int64)
    for _ in range(d):
        p = rng.permutation(r)
        M[np.arange(r), p] += 1
    return M


def candidate_groups(rng):
    """(r, m, k, lam) tuples with r*... such that the lift order 2*r*(m*k) exceeds 4000."""
    out = []
    for r in (2, 3, 4):
        nmin = 4000 // (2 * r) + 1
        for N in range(nmin, nmin + 30):
            for k in range(1, N + 1):
                if N % k:
                    continue
                m = N // k
                if m < 2:
                    continue
                if k == 1:
                    lams = [1]
                else:
                    cand = [l for l in range(2, m) if math.gcd(l, m) == 1 and pow(l, k, m) == 1 % m]
                    if not cand:
                        continue
                    pick = rng.choice(len(cand), size=min(2, len(cand)), replace=False)
                    lams = [cand[int(t)] for t in pick]
                for lam in lams:
                    out.append((r, m, k, lam))
    return out


# ------------------------------------------------------------------------------- voltage-lift annealing

class Lift:
    """Annealing state: voltages V[i][j] (distinct group elements) for the M[i][j] darts from A_i to B_j."""

    def __init__(self, r, N, MT, inv, M, d, D, rng, T):
        self.r, self.N, self.MT, self.inv, self.M = r, N, MT, inv, M
        self.d, self.D, self.rng, self.T = d, D, rng, T
        self.total = 2 * r * N
        self.blocks = [(i, j) for i in range(r) for j in range(r) if M[i][j] > 0]
        self.best = 10 ** 9
        self.bestV = None
        self.restart()

    def random_V(self):
        return [[[int(x) for x in self.rng.choice(self.N, size=int(self.M[i][j]), replace=False)]
                 for j in range(self.r)] for i in range(self.r)]

    def nb(self, V):
        r, N, MT, inv = self.r, self.N, self.MT, self.inv
        NB = np.empty((self.total, self.d), dtype=np.int64)
        for i in range(r):
            c = 0
            for j in range(r):
                for x in V[i][j]:
                    NB[i * N:(i + 1) * N, c] = (r + j) * N + MT[x]
                    c += 1
        for j in range(r):
            c = 0
            for i in range(r):
                for x in V[i][j]:
                    NB[(r + j) * N:(r + j + 1) * N, c] = i * N + MT[inv[x]]
                    c += 1
        return NB

    def cost(self, V):
        NB = self.nb(V)
        T_ = self.total
        c = 0
        for b in range(2 * self.r):
            s = b * self.N
            vis = np.zeros(T_, dtype=bool)
            vis[s] = True
            fr = np.array([s], dtype=np.int64)
            for _ in range(self.D):
                nxt = NB[fr].ravel()
                nxt = nxt[~vis[nxt]]
                if nxt.size == 0:
                    break
                fr = np.unique(nxt)
                vis[fr] = True
            c += T_ - int(vis.sum())
        return c

    def _record(self):
        if self.cur < self.best:
            self.best = self.cur
            self.bestV = [[list(x) for x in row] for row in self.V]

    def restart(self):
        self.V = self.random_V()
        self.cur = self.cost(self.V)
        self.since = 0
        self._record()

    def step(self):
        i, j = self.blocks[int(self.rng.integers(len(self.blocks)))]
        lst = self.V[i][j]
        p = int(self.rng.integers(len(lst)))
        old = lst[p]
        y = int(self.rng.integers(self.N))
        while y in lst:
            y = int(self.rng.integers(self.N))
        lst[p] = y
        c = self.cost(self.V)
        delta = c - self.cur
        if delta <= 0 or self.rng.random() < math.exp(-delta / self.T):
            if delta < 0:
                self.since = 0
            else:
                self.since += 1
            self.cur = c
            self._record()
        else:
            lst[p] = old
            self.since += 1

    def run_until(self, stop):
        while self.best > 0 and time.monotonic() < stop:
            self.step()
            if self.since > PATIENCE:
                self.restart()

    def graph(self):
        r, N, MT = self.r, self.N, self.MT
        edges = []
        for i in range(r):
            for j in range(r):
                for x in self.bestV[i][j]:
                    col = ((r + j) * N + MT[x]).tolist()
                    for g in range(N):
                        edges.append((i * N + g, col[g]))
        return 2 * r * N, edges


def search_lifts(d, D, rng, end):
    cands = candidate_groups(rng)
    order = rng.permutation(len(cands))
    runs = []
    for idx in order:
        if len(runs) >= MAX_RUNS:
            break
        r, m, k, lam = cands[int(idx)]
        try:
            MT, inv = group_meta(m, k, lam)
            M = block_counts(r, d, rng)
            runs.append(Lift(r, m * k, MT, inv, M, d, D, rng, float(rng.uniform(0.3, 1.5))))
        except Exception:
            continue
    q = 0.5
    active = runs
    while active and time.monotonic() < end:
        for run in active:
            now = time.monotonic()
            if now >= end:
                break
            run.run_until(min(end, now + q))
            if run.best == 0:
                try:
                    n, edges = run.graph()
                    if lib.is_valid(n, edges, d, D):
                        return n, edges
                except Exception:
                    pass
                run.best = 10 ** 9
        active = sorted(active, key=lambda x: x.best)
        if len(active) > 4:
            active = active[:max(2, (len(active) + 1) // 2)]
        q *= 1.5
    return None


# ----------------------------------------------------------------------------------- fallback

def fallback_haar(d, D):
    """Parent's valid Haar graph (order 2*1791), checked before it is returned."""
    MT, _ = group_meta(199, 9, 180)
    N = MT.shape[0]
    edges = []
    for s in sorted(set(FALLBACK_S)):
        for g in range(N):
            edges.append((g, N + int(MT[s, g])))
    n = 2 * N
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


# -------------------------------------------------------------------------------------------- entry

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    end = t0 + SEARCH_FRAC * time_limit
    rng = np.random.default_rng(seed)
    try:
        g = search_lifts(d, D, rng, end)
        if g is not None:
            return g
    except Exception:
        pass
    try:
        fb = fallback_haar(d, D)
        if fb is not None:
            return fb
    except Exception:
        pass
    return trivial(d, D)
