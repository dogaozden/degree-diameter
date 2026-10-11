import math
import random
import time

import numpy as np

import lib

# Popcount table for uint8 values.
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ----------------------------------------------------------------------------
# Structured candidates (cheap, used as baselines).
# ----------------------------------------------------------------------------

def _pg_candidate(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power (meets the Moore bound for D = 3)."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# NEW CONSTRUCTION (bold change): fixed-order bipartite annealing.
#
# Instead of searching group-invariant voltage lifts, we fix the order
# N = 2h and anneal over ALL d-regular bipartite graphs on h + h vertices,
# moved by degree-preserving 2-switches. The cost is the number of ordered
# vertex pairs at distance > D, computed with packed uint64 bitsets in numpy
# (a full evaluation is about a millisecond at N ~ 700). The order h is
# raised by bisection between the largest success and the smallest failure.
# ----------------------------------------------------------------------------

def _init_adj(h, d, rng):
    """Circulant d-regular bipartite start: left a ~ right h+(a+o)%h for distinct offsets o."""
    N = 2 * h
    adj = np.empty((N, d), dtype=np.int64)
    offs = rng.sample(range(h), d)
    a = np.arange(h, dtype=np.int64)
    for k, o in enumerate(offs):
        adj[:h, k] = h + (a + o) % h
        adj[h:, k] = (a - o) % h
    return adj


def _cost(adj, N, D):
    """Ordered pairs (u, v) with dist(u, v) > D. Zero means diameter <= D."""
    W = (N + 63) >> 6
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        nxt = reach | np.bitwise_or.reduce(reach[adj], axis=1)
        if np.array_equal(nxt, reach):
            break
        reach = nxt
    total = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - total


def _propose(adj, h, d, rng):
    """Random 2-switch between left-right edges (a,b), (c,e) -> (a,e), (c,b). Returns undo info or None."""
    a = rng.randrange(h)
    c = rng.randrange(h)
    if a == c:
        return None
    ka = rng.randrange(d)
    kc = rng.randrange(d)
    b = int(adj[a, ka])
    e = int(adj[c, kc])
    if np.any(adj[a] == e) or np.any(adj[c] == b):
        return None
    kb = int(np.flatnonzero(adj[b] == a)[0])
    ke = int(np.flatnonzero(adj[e] == c)[0])
    adj[a, ka] = e
    adj[c, kc] = b
    adj[b, kb] = c
    adj[e, ke] = a
    return (a, ka, b, kb, c, kc, e, ke)


def _undo(adj, mv):
    a, ka, b, kb, c, kc, e, ke = mv
    adj[a, ka] = b
    adj[c, kc] = e
    adj[b, kb] = a
    adj[e, ke] = c


def _anneal(h, d, D, rng, deadline):
    """Anneal a d-regular bipartite graph on h+h vertices to diameter <= D. Returns adj or None."""
    N = 2 * h
    adj = _init_adj(h, d, rng)
    for _ in range(3 * N):  # randomize the start
        _propose(adj, h, d, rng)
    cur = _cost(adj, N, D)
    T0 = 2.0
    T = T0
    it = 0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        it += 1
        if it % 20000 == 0:  # periodic reheat
            T = T0
        T = max(0.03, T * 0.9995)
        mv = _propose(adj, h, d, rng)
        if mv is None:
            continue
        new = _cost(adj, N, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cur = new
        else:
            _undo(adj, mv)
    return adj


def _edges(adj, h):
    """Edge list from the adjacency array; left vertices are 0..h-1."""
    E = [(a, int(b)) for a in range(h) for b in adj[a].tolist()]
    return adj.shape[0], E


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 0.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = lib.haar_graph(D, [0, 1])  # even cycle C_{2D}, diameter D
        if lib.is_valid(n, e, d, D):
            return n, e
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D == 2:
        return best

    moore = lib.moore_bound(d, D)

    if D == 3:
        pg = _pg_candidate(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if best_n >= moore:
            return best
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                ar = lib.araujo_lopez_graph(q)
                consider(ar[0], ar[1])
            except Exception:
                pass

    # Bisection over the number of left vertices h (order N = 2h).
    # h_ok: largest order that succeeded; h_fail: smallest order that failed.
    attempt_cap = max(2.0, 0.12 * (deadline - start))
    half_max = moore // 2
    h_ok = best_n // 2
    h_fail = float("inf")
    h = h_ok + max(1, h_ok // 12)

    while time.monotonic() < deadline and h <= half_max:
        adj = _anneal(h, d, D, rng, min(deadline, time.monotonic() + attempt_cap))
        if adj is not None:
            N, E = _edges(adj, h)
            consider(N, E)
            h_ok = h
            if h_fail <= h_ok:
                h_fail = float("inf")
        else:
            h_fail = min(h_fail, h)

        if h_fail == float("inf"):
            h = h_ok + max(1, h_ok // 12)
        else:
            h = max(h_ok + 1, (h_ok + h_fail) // 2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
