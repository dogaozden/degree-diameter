"""Haar-graph annealing over small non-abelian groups for the d=10, D=5 target.

CONSTRUCTION (new relative to the parent).  The parent samples random bipartite regular graphs. This
program instead searches Haar graphs H(G, S) over metacyclic groups G = Z_m x| Z_k with |G| = m*k
slightly above 2000, so 2|G| exceeds the record 4000. Vertices are (g, A) and (g, B), with edges
(g, A) ~ (s*g, B) for s in S. The graph is bipartite and d-regular, and it has diameter at most 5 iff
(S^-1 S)^2 = G and (S S^-1)^2 = G. The cost is the number of uncovered group elements in those two
squared sets. Cost 0 gives a valid graph, which is still checked exactly with lib.is_valid.

SEARCH.  Candidate groups come lazily from two tiers, interleaved: orders 2001..2120 first (these beat
the record), then 1792..2000 (these beat the fallback). A small pool of groups is annealed round-robin,
each with Metropolis moves on one element of S and restarts when stalled. A group retires after a fixed
step budget and is replaced from the queue. Once a valid order is found, slots with orders not above it
are dropped.

SAFETY.  The valid Haar fallback (order 3582) is verified first. Only graphs passing lib.is_valid are
returned. Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


TARGET = (10, 5)
POOL = 5          # groups annealed at the same time
CHUNK = 300       # steps per round-robin visit
PATIENCE = 30000  # steps before a group is retired
STALL = 3000      # steps without improvement before a restart
TEMP = 1.0        # Metropolis temperature
KMAX = 12         # largest Z_k factor tried


# ----------------------------------------------------------------------------- group tables

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


def haar_edges(MT, S):
    """Edges of the Haar graph: A-vertex g is g, B-vertex g is N+g, (g, A) ~ (s*g, B)."""
    N = MT.shape[0]
    S = sorted({int(s) for s in S})
    g = np.arange(N)
    return 2 * N, [(int(a), int(N + b)) for s in S for a, b in zip(g, MT[s])]


def checked(MT, S, d, D):
    """The Haar graph for S, or None if it is not exactly valid."""
    n, edges = haar_edges(MT, S)
    return (n, edges) if lib.is_valid(n, edges, d, D) else None


def trivial(d, D):
    """Always-valid small graph for any other (d, D) the evaluator may ask for."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


# Valid smaller Haar graph (order 3582), checked at run time; baseline if the search fails.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


# ----------------------------------------------------------------------- candidate groups

def gen_tier(Ns):
    """Yield (N, m, k, lam) for non-abelian Z_m x|_lam Z_k with N = m*k, lam != 1, lam^k = 1 mod m (lazy)."""
    for N in Ns:
        for k in range(2, KMAX + 1):
            if N % k:
                continue
            m = N // k
            if m < 3:
                continue
            cnt = 0
            for lam in range(2, m):
                if math.gcd(lam, m) == 1 and pow(lam, k, m) == 1:
                    yield (N, m, k, lam)
                    cnt += 1
                    if cnt == 2:
                        break


def candidates():
    """Interleave the tier of orders 2001..2120 (beats the record) with orders 1792..2000 (beats the fallback)."""
    gens = [gen_tier(range(2001, 2121)), gen_tier(range(2000, 1791, -1))]
    while gens:
        for g in list(gens):
            try:
                yield next(g)
            except StopIteration:
                gens.remove(g)


# --------------------------------------------------------------------------- annealing slot

class Slot:
    """One group under annealing: a connection set S of d group elements with an incremental-free cost."""

    def __init__(self, cand, d, rng):
        self.N, self.m, self.k, self.lam = cand
        self.d = d
        self.rng = rng
        self.MT = None
        self.inv = None
        self.steps = 0
        self.dead = False
        self.S = None
        self.cost = None
        self.best = None
        self.stall = 0

    def _restart(self):
        self.S = self.rng.choice(self.N, size=self.d, replace=False).astype(np.int64)
        self.cost = self.evaluate(self.S)
        self.best = self.cost
        self.stall = 0

    def evaluate(self, S):
        """Number of uncovered elements of (S^-1 S)^2 plus those of (S S^-1)^2."""
        MT, inv, N = self.MT, self.inv, self.N
        iS = inv[S]
        T1 = np.unique(MT[iS[:, None], S[None, :]].ravel())        # s^-1 t
        cov = np.zeros(N, dtype=bool)
        cov[MT[T1[:, None], T1[None, :]].ravel()] = True
        c1 = N - int(cov.sum())
        T2 = np.unique(MT[S[:, None], iS[None, :]].ravel())        # s t^-1
        cov[:] = False
        cov[MT[T2[:, None], T2[None, :]].ravel()] = True
        c2 = N - int(cov.sum())
        return c1 + c2

    def run(self, chunk, d, D):
        """Advance the annealing by up to `chunk` steps. Returns a validated (n, edges) on success, else None."""
        if self.MT is None:
            self.MT, self.inv = group_meta(self.m, self.k, self.lam)
            self._restart()
        for _ in range(chunk):
            self.steps += 1
            if self.steps > PATIENCE:
                self.dead = True
                return None
            if self.cost == 0:
                n, edges = haar_edges(self.MT, self.S)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
                self._restart()
                continue
            if self.stall >= STALL:
                self._restart()
                continue
            p = int(self.rng.integers(d))
            x = int(self.rng.integers(self.N))
            if np.any(self.S == x):
                self.stall += 1
                continue
            S2 = self.S.copy()
            S2[p] = x
            c = self.evaluate(S2)
            delta = c - self.cost
            if delta <= 0 or self.rng.random() < math.exp(-delta / TEMP):
                self.S = S2
                self.cost = c
            if self.cost < self.best:
                self.best = self.cost
                self.stall = 0
            else:
                self.stall += 1
        return None


def anneal(d, D, deadline, rng, floor_N):
    """Round-robin annealing over lazily generated groups. Returns the largest validated (n, edges), or None."""
    best = None
    best_N = floor_N
    cands = candidates()
    pool = []

    def refill():
        while len(pool) < POOL:
            c = next(cands, None)
            if c is None:
                return
            if c[0] <= best_N:
                continue
            pool.append(Slot(c, d, rng))

    refill()
    while pool and time.monotonic() < deadline:
        for slot in list(pool):
            if time.monotonic() >= deadline:
                break
            if slot.N <= best_N:
                if slot in pool:
                    pool.remove(slot)
                continue
            try:
                res = slot.run(CHUNK, d, D)
            except Exception:
                res = None
                slot.dead = True
            if res is not None:
                best = res
                best_N = slot.N
                pool[:] = [s for s in pool if s.N > best_N]
                break
            if slot.dead and slot in pool:
                pool.remove(slot)
        refill()
    return best


# ------------------------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    budget = max(2.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    floor_N = best[0] // 2 if best is not None else 0
    try:
        found = anneal(d, D, deadline, rng, floor_N)
    except Exception:
        found = None

    if found is not None:
        return found
    if best is not None:
        return best
    return trivial(d, D)
