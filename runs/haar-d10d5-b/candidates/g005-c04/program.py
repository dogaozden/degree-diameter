"""Non-abelian Haar-graph search for the bipartite degree-diameter problem (d=10, D=5).

CONSTRUCTION.  A Haar graph over a group G with connection set S (|S| = d) has vertices A_g, B_g (g in G) and
edges A_g ~ B_{s*g} for s in S.  It is bipartite, d-regular and simple when S has distinct elements.  Left
translating S by x leaves the cover condition unchanged, so WLOG the identity is in S.

PROVED CRITERION.  The diameter is at most 5 iff (S^-1 S)^2 = G and (S S^-1)^2 = G.  The search cost is the number
of uncovered elements of these two sets, and cost 0 means a valid graph of order 2|G|.

SEARCH.  The groups are metacyclic Z_m x| Z_k (r != 1, so non-abelian), with orders just above the current best.
Each task runs a small best-of-3 simulated annealing over the non-identity elements of S, with random restarts when
stalled.  Tasks are run round-robin.  The order window moves up as valid graphs are found.  Every candidate is
verified with lib.is_valid before it is accepted.

SAFETY.  The parent's valid Haar graph (group order 1791, 3582 vertices) is verified first and is the fallback, so
the output is never worse than the parent's.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
POOL = 5
WINDOW = 40
STEPS_PER_TURN = 300
STALL_LIMIT = 30000

FALLBACK_GROUP = (199, 9, 180)
FALLBACK_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]

_CAND_CACHE = {}


def trivial(d, D):
    """Always-valid small graph for any other (d, D)."""
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
        return lib.projective_plane_incidence(d - 1)
    return lib.haar_graph(d, range(d))


def group_table(m, k, r):
    """Z_m x|_r Z_k with element (a, j) -> a*k + j, (a, j)(b, l) = (a + r^j b, j + l).  Returns (MT, inv)."""
    N = m * k
    pw = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    idx = np.arange(N, dtype=np.int64)
    ak = idx // k
    jk = idx % k
    MT = np.empty((N, N), dtype=np.int32)
    step = 128
    for lo in range(0, N, step):
        hi = min(N, lo + step)
        a = ak[lo:hi, None]
        j = jk[lo:hi, None]
        MT[lo:hi] = ((a + pw[j] * ak[None, :]) % m) * k + (j + jk[None, :]) % k
    inv = np.argmax(MT == 0, axis=1).astype(np.int64)
    return MT, inv


def candidate_groups(N):
    """All (m, k, r) with m*k = N, k >= 2, r a non-trivial unit with r^k = 1 mod m."""
    if N in _CAND_CACHE:
        return _CAND_CACHE[N]
    out = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(2, m):
            if math.gcd(r, m) != 1:
                continue
            if pow(r, k, m) != 1 % m:
                continue
            out.append((m, k, r))
    _CAND_CACHE[N] = out
    return out


def haar_from(MT, S, N):
    """Haar graph of the table group: (g, A) ~ (s*g, B), vertices A = g, B = N + g."""
    ar = np.arange(N, dtype=np.int64)
    edges = []
    for s in sorted(set(int(x) for x in S)):
        edges.extend(zip(ar.tolist(), (N + MT[s].astype(np.int64)).tolist()))
    return 2 * N, edges


class Search:
    """Simulated annealing over S (S[0] = identity) for the Haar cover criterion."""

    def __init__(self, MT, inv, N, d, rng):
        self.MT = MT
        self.inv = inv
        self.N = N
        self.d = d
        self.rng = rng
        self.reset()

    def cost(self, S):
        MT = self.MT
        Si = self.inv[S]
        D1 = MT[Si[:, None], S[None, :]].ravel()   # s^-1 t
        D2 = MT[S[:, None], Si[None, :]].ravel()   # s t^-1
        c = 0
        for Dset in (D1, D2):
            P = MT[Dset[:, None], Dset[None, :]].ravel()
            c += self.N - int(np.count_nonzero(np.bincount(P, minlength=self.N)))
        return int(c)

    def reset(self):
        S = np.empty(self.d, dtype=np.int64)
        S[0] = 0
        S[1:] = self.rng.choice(np.arange(1, self.N), self.d - 1, replace=False)
        self.S = S
        self.cur = self.cost(S)
        self.best = self.cur
        self.stall = 0

    def step(self):
        """One annealing move.  Returns True when a zero-cost S has been reached."""
        if self.cur == 0:
            return True
        if self.stall > STALL_LIMIT:
            self.reset()
            return self.cur == 0
        S = self.S
        best_c = None
        best_i = None
        best_g = None
        for _ in range(3):
            i = int(self.rng.integers(1, self.d))
            g = int(self.rng.integers(self.N))
            if np.any(S == g):
                continue
            old = S[i]
            S[i] = g
            c = self.cost(S)
            S[i] = old
            if best_c is None or c < best_c:
                best_c, best_i, best_g = c, i, g
        if best_c is None:
            self.stall += 1
            return False
        T = 0.7
        if best_c <= self.cur or self.rng.random() < math.exp(-(best_c - self.cur) / T):
            S[best_i] = best_g
            self.cur = best_c
        if self.cur < self.best:
            self.best = self.cur
            self.stall = 0
        else:
            self.stall += 1
        return self.cur == 0


def spawn(best_N, rng, d):
    """A fresh task whose group order lies just above best_N."""
    extra = 0
    while True:
        hi = best_N + WINDOW * (1 + extra)
        options = []
        for _ in range(60):
            N = int(rng.integers(best_N + 1, hi + 1))
            cands = candidate_groups(N)
            if cands:
                options.append((N, cands))
                break
        if options:
            N, cands = options[0]
            m, k, r = cands[int(rng.integers(len(cands)))]
            MT, inv = group_table(m, k, r)
            return {'N': N, 'MT': MT, 'search': Search(MT, inv, N, d, rng)}
        extra += 1


def build(d, D, seed, time_limit):
    if (d, D) != TARGET:
        return trivial(d, D)
    t0 = time.monotonic()
    budget = max(2.0, min(0.80 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = np.random.default_rng(seed)

    best_n, best_edges, best_N = 0, None, 0
    try:
        m, k, r = FALLBACK_GROUP
        MT, _ = group_table(m, k, r)
        n, e = haar_from(MT, FALLBACK_S, m * k)
        if lib.is_valid(n, e, d, D):
            best_n, best_edges, best_N = n, e, m * k
    except Exception:
        pass

    pool = []
    for _ in range(POOL):
        try:
            pool.append(spawn(best_N, rng, d))
        except Exception:
            pass

    while time.monotonic() < deadline and pool:
        for idx in range(len(pool)):
            if time.monotonic() >= deadline:
                break
            task = pool[idx]
            if task['N'] <= best_N:
                try:
                    pool[idx] = spawn(best_N, rng, d)
                except Exception:
                    pool[idx] = task
                continue
            found = False
            try:
                for _ in range(STEPS_PER_TURN):
                    if task['search'].step():
                        found = True
                        break
            except Exception:
                found = False
                try:
                    pool[idx] = spawn(best_N, rng, d)
                except Exception:
                    pass
                continue
            if found:
                N = task['N']
                try:
                    n, e = haar_from(task['MT'], task['search'].S, N)
                    ok = n > best_n and lib.is_valid(n, e, d, D)
                except Exception:
                    ok = False
                if ok:
                    best_n, best_edges, best_N = n, e, N
                try:
                    pool[idx] = spawn(best_N, rng, d)
                except Exception:
                    pass

    if best_edges is None:
        return trivial(d, D)
    return best_n, best_edges
