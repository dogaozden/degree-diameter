import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: incidence graph of PG(2, q), with q the largest prime power <= d-1.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-Cayley graphs over finite groups.
#
# Group G of order N. Vertices A_g = g and B_h = N + h. For a connection set
# S of d distinct elements, A_g is joined to B_{g*s} for every s in S.
# Every vertex has degree d, the graph is bipartite, and left multiplication
# by a group element is an automorphism that preserves each side. So the
# diameter can be checked with two BFS runs, from A_e and B_e.
# WLOG the identity lies in S (relabel B_h -> B_{h t} to shift S by t).
# Groups are semidirect products Z_m x| Z_k (cyclic when k = 1).
# ----------------------------------------------------------------------------

class _Group:
    """Finite group of order n with multiplication, inverses and cached right-multiplication maps."""

    def __init__(self, order, mul, inv):
        self.n = order
        self.mul = mul
        self.inv = [inv(x) for x in range(order)]
        self._rp = {}

    def rp(self, s):
        """Permutation g -> g*s of the group, cached."""
        p = self._rp.get(s)
        if p is None:
            mul = self.mul
            p = [mul(g, s) for g in range(self.n)]
            self._rp[s] = p
        return p


def _groups_of_order(N, rng, limit):
    """Up to `limit` random groups of order N, drawn from cyclic and semidirect Z_m x| Z_k."""
    cands = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            cands.append((N, 1, 1))
        elif m >= 2:
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    cands.append((m, k, r))
    rng.shuffle(cands)
    groups = []
    for m, k, r in cands[:limit]:
        order, mul, inv = lib.semidirect_group(m, k, r)
        groups.append(_Group(order, mul, inv))
    return groups


def _cayley_adj(grp, S):
    """Adjacency lists of the bi-Cayley graph with connection set S (A = 0..N-1, B = N..2N-1)."""
    N = grp.n
    adj = [[] for _ in range(2 * N)]
    for s in S:
        ps = grp.rp(s)
        pi = grp.rp(grp.inv[s])
        for g in range(N):
            adj[g].append(N + ps[g])
        for h in range(N):
            # B_h is joined to A_{h s^{-1}}
            adj[N + h].append(pi[h])
    return adj


def _unreached(adj, total, D, src):
    """Number of vertices not within distance D of src."""
    seen = [False] * total
    seen[src] = True
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = True
                    nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return total - count


def _cost(grp, S, D):
    """Zero iff the bi-Cayley graph with connection set S has diameter <= D."""
    N = grp.n
    adj = _cayley_adj(grp, S)
    return _unreached(adj, 2 * N, D, 0) + _unreached(adj, 2 * N, D, N)


def _climb(grp, d, D, rng, deadline, steps):
    """Plateau-walking search over connection sets containing the identity; returns S or None."""
    N = grp.n
    if N < d:
        return None
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(grp, S, D)
    for _ in range(steps):
        if cur == 0:
            return S
        if time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(N)
        if x in S:
            continue
        T = S[:]
        T[i] = x
        c2 = _cost(grp, T, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur)):
            S, cur = T, c2
    return S if cur == 0 else None


def _cayley_window(d, D, lo, hi, rng, deadline):
    """Try orders N = hi, hi-1, ..., lo+1 in that order; return (2N, edges) for the first success."""
    for N in range(hi, lo, -1):
        now = time.monotonic()
        if now >= deadline:
            break
        if 2 * N * d > 60000:
            continue
        slot_end = now + (deadline - now) / (N - lo)
        groups = _groups_of_order(N, rng, 10)
        found = None
        attempt = 0
        while found is None and groups and time.monotonic() < slot_end:
            grp = groups[attempt % len(groups)]
            attempt += 1
            S = _climb(grp, d, D, rng, slot_end, 3000)
            if S is not None:
                found = (grp, S)
        if found is not None:
            grp, S = found
            edges = []
            for s in S:
                ps = grp.rp(s)
                for g in range(N):
                    edges.append((g, N + ps[g]))
            if lib.is_valid(2 * N, edges, d, D):
                return 2 * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Baseline from the projective plane (diameter 3).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: bi-Cayley graphs over groups, each order window seeded by the current best.
    # A success at order N gives 2N vertices, so every accepted graph strictly improves the best.
    if d >= 2:
        cdead = start + 0.7 * time_limit
        while time.monotonic() < cdead:
            lo = best_n // 2
            moore = lib._moore_bound(d, D)
            hi = min(moore // 2, lo + 40)
            if hi <= lo:
                break
            res = _cayley_window(d, D, lo, hi, rng, cdead)
            if res is None:
                break
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
