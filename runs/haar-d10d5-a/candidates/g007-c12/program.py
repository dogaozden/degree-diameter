"""Bipartite degree-diameter search for the d=10, D=5 target, using annealed Haar graphs over metacyclic groups.

NEW IDEA (not in the parent).  A Haar graph over a group G with connection set S (|S| = d) has 2|G| vertices
and diameter at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The parent only uses random bipartite
regular graphs plus one fixed Haar graph.  This program searches Haar graphs directly:

  * cover_cost(S) = (|G| - |(S^-1 S)^2|) + (|G| - |(S S^-1)^2|), computed with table lookups and boolean
    marking.  It is zero exactly when the Haar graph has diameter <= 5.
  * Simulated annealing on S: replace one slot with a random element of G, accept by Metropolis, restart
    after a long stall.
  * Several non-abelian metacyclic groups Z_m x|_lam Z_k with order in [2001, 2040] run round-robin, so
    every success beats the record order 4000 (group order > 2000).  Once a group succeeds, groups of
    order no larger than the new best are dropped.

SAFETY.  The verified Haar fallback (order 3582) is checked first.  Any search result must pass lib.is_valid
before it replaces the best graph.  Other (d, D) cases return a small always-valid graph.
"""
import math
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------- small valid graphs

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


# ------------------------------------------------------------- NEW: Haar cover cost and annealing

def cover_cost(MT, inv, N, S):
    """Number of group elements missing from (S^-1 S)^2 plus those missing from (S S^-1)^2.

    Zero iff the Haar graph with connection set S has diameter <= 5.
    """
    Si = inv[S]
    X = np.unique(MT[Si[:, None], S[None, :]])     # s^-1 t
    Y = np.unique(MT[S[:, None], Si[None, :]])     # s t^-1
    c = 0
    for Z in (X, Y):
        cov = np.zeros(N, dtype=bool)
        cov[MT[Z[:, None], Z[None, :]].ravel()] = True
        c += N - int(cov.sum())
    return c


class _HaarSearch:
    """Simulated annealing over connection sets of one metacyclic group."""

    def __init__(self, m, k, lam, d, rng):
        self.MT, self.inv = group_meta(m, k, lam)
        self.N = m * k
        self.order = self.N
        self.d = d
        self.rng = rng
        self.T = 0.6
        self.restart()

    def restart(self):
        self.S = self.rng.choice(self.N, size=self.d, replace=False).astype(np.int64)
        self.c = cover_cost(self.MT, self.inv, self.N, self.S)
        self.best_c = self.c
        self.stall = 0

    def step(self, iters):
        """Run up to iters annealing moves. Return True if a zero-cost set is reached."""
        for _ in range(iters):
            if self.c == 0:
                return True
            i = int(self.rng.integers(self.d))
            g = int(self.rng.integers(self.N))
            if np.any(self.S == g):
                continue
            S2 = self.S.copy()
            S2[i] = g
            c2 = cover_cost(self.MT, self.inv, self.N, S2)
            if c2 <= self.c or self.rng.random() < math.exp(-(c2 - self.c) / self.T):
                self.S, self.c = S2, c2
                if c2 < self.best_c:
                    self.best_c = c2
                    self.stall = 0
            self.stall += 1
            if self.stall > 4000:
                self.restart()
        return self.c == 0


def group_pool(d, rng, lo_N=2001, hi_N=2040, limit=8):
    """Non-abelian metacyclic groups Z_m x|_lam Z_k with order in [lo_N, hi_N], shuffled and truncated."""
    pool = []
    for k in range(2, 16):
        for m in range(max(2, -(-lo_N // k)), hi_N // k + 1):
            N = m * k
            if N < lo_N or N > hi_N:
                continue
            for lam in range(2, m):
                if lam % m != 1 and math.gcd(lam, m) == 1 and pow(lam, k, m) == 1 % m:
                    pool.append((m, k, lam))
    if not pool:
        return []
    order = rng.permutation(len(pool))
    return [pool[int(i)] for i in order[:limit]]


# ------------------------------------------------------------- random bipartite regular graphs (parent)

def random_bipartite(k, d, rng):
    """Simple d-regular bipartite graph on k+k vertices (A = 0..k-1, B = k..2k-1), as a union of d
    permutation matchings with repairs to avoid repeated edges.  Returns an edge list, or None on failure."""
    used = set()
    for _ in range(d):
        perm = [int(x) for x in rng.permutation(k)]
        bad = [i for i in range(k) if i * k + perm[i] in used]
        steps = 0
        while bad:
            steps += 1
            if steps > 200000:
                return None
            i = bad.pop()
            if i * k + perm[i] not in used:
                continue
            j = int(rng.integers(k))
            if j == i:
                continue
            perm[i], perm[j] = perm[j], perm[i]
            if (i * k + perm[i] in used) or (j * k + perm[j] in used):
                perm[i], perm[j] = perm[j], perm[i]
                bad.append(i)
        for i in range(k):
            used.add(i * k + perm[i])
    return [(c // k, k + c % k) for c in used]


# ------------------------------------------------------------------------------------- entry point

TARGET = (10, 5)

# Valid smaller Haar graph (order 3582), checked at run time.
FALLBACK = (lambda: group_meta(199, 9, 180), [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314])


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)

    t0 = time.monotonic()
    deadline = t0 + max(2.0, min(0.7 * time_limit, time_limit - 12.0))
    rng = np.random.default_rng(seed)

    best = None
    try:
        MT, _ = FALLBACK[0]()
        best = checked(MT, FALLBACK[1], d, D)
    except Exception:
        best = None

    searches = []
    try:
        for m, k, lam in group_pool(d, rng):
            if time.monotonic() > deadline - 2.0:
                break
            try:
                searches.append(_HaarSearch(m, k, lam, d, rng))
            except Exception:
                continue
    except Exception:
        searches = []

    try:
        while searches and time.monotonic() < deadline:
            best_order = best[0] // 2 if best is not None else 0
            searches = [s for s in searches if s.order > best_order]
            for s in list(searches):
                if time.monotonic() >= deadline:
                    break
                if s.step(200):
                    try:
                        n, e = haar_edges(s.MT, s.S)
                        if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
                            best = (n, e)
                    except Exception:
                        pass
                    s.restart()
                    if s.c == 0:
                        # A zero-cost set was validated (or rejected); drop this group from the pool
                        searches = [x for x in searches if x is not s]
                        break
    except Exception:
        pass

    if best is not None and lib.is_valid(best[0], best[1], d, D):
        return best
    return trivial(d, D)
