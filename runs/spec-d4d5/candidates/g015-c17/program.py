import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold family: single-orbit bipartite Cayley-type graphs (bi-Cayley graphs over
# a group G of order N). Vertices A_g = g and B_h = N + h. Connection set S of
# size d gives edges A_g -- B_{g*s} for s in S. Left multiplication by G is an
# automorphism acting transitively on each side, so diameter <= D is equivalent
# to: the identity of A and the identity of B reach everything within D steps.
# The search is simulated annealing over S, over many non-abelian groups
# Z_m x| Z_k of the target order.
# ----------------------------------------------------------------------------

def _group_options(N, rng, limit=40):
    """Valid (m, k, r) with m * k = N giving semidirect products Z_m x| Z_k (random sample)."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        if k == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                opts.append((m, k, r))
    if len(opts) > limit:
        opts = rng.sample(opts, limit)
    return opts


def _mult_tables(m, k, r):
    """Return (N, T, inv) with T[x][y] = x*y and inv[x] = x^{-1}, identity = index 0."""
    order, mul, inv_fn = lib.semidirect_group(m, k, r)
    N = order
    T = [[mul(x, y) for y in range(N)] for x in range(N)]
    inv = [inv_fn(x) for x in range(N)]
    return N, T, inv


def _adj(N, T, inv, S):
    """Adjacency lists of the bi-Cayley graph on 2N vertices (A = 0..N-1, B = N..2N-1)."""
    adj = [None] * (2 * N)
    invS = [inv[s] for s in S]
    for g in range(N):
        Tg = T[g]
        adj[g] = [N + Tg[s] for s in S]
    for h in range(N):
        Th = T[h]
        adj[N + h] = [Th[t] for t in invS]
    return adj


def _unreached(adj, total, src, D):
    """Number of vertices not reached from src within D steps."""
    seen = bytearray(total)
    seen[src] = 1
    frontier = [src]
    count = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not seen[v]:
                    seen[v] = 1
                    nxt.append(v)
        if not nxt:
            break
        count += len(nxt)
        frontier = nxt
    return total - count


def _cost(N, T, inv, S, D):
    adj = _adj(N, T, inv, S)
    return _unreached(adj, 2 * N, 0, D) + _unreached(adj, 2 * N, N, D)


def _anneal_connection(d, D, N, T, inv, rng, deadline, iters):
    """Simulated annealing over a connection set S of size d in G; returns S or None."""
    if N < d:
        return None
    S = rng.sample(range(N), d)
    cur = _cost(N, T, inv, S, D)
    t0, t1 = 1.5, 0.05
    for it in range(iters):
        if cur == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = t0 * (t1 / t0) ** (it / max(1, iters))
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        new = S[:]
        new[i] = x
        c2 = _cost(N, T, inv, new, D)
        delta = c2 - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = new, c2
    return S if cur == 0 else None


def _edges_from(N, T, S):
    return [(g, N + T[g][s]) for g in range(N) for s in S]


# ----------------------------------------------------------------------------
# Safe baselines.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is valid for every D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    moore = lib._moore_bound(d, D)

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    # Main search: single-orbit bi-Cayley graphs over non-abelian groups.
    while time.monotonic() < deadline and best_n < moore:
        # Target a group order whose bi-Cayley graph would beat the current best.
        N = max(d, best_n // 2 + 1 + rng.randrange(0, 4))
        opts = _group_options(N, rng)
        if not opts:
            continue
        m, k, r = rng.choice(opts)
        try:
            gN, T, inv = _mult_tables(m, k, r)
        except ValueError:
            continue
        if gN != N:
            continue
        remaining = deadline - time.monotonic()
        if remaining <= 0:
            break
        attempt_deadline = time.monotonic() + min(remaining, 4.0)
        S = _anneal_connection(d, D, N, T, inv, rng, attempt_deadline, iters=1500)
        if S is not None:
            consider(2 * N, _edges_from(N, T, S))

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
