import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe algebraic baselines (valid for D >= 3): projective plane incidence and
# the Araujo-Pardo-Lopez graph.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New construction: d-regular bipartite graphs found by local search directly
# on the graph (no group structure).
#
# Vertex ids: A-vertex a -> 2a, B-vertex b -> 2b+1. Every vertex has degree d.
# Moves: double-edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1), which keep
# the graph simple, bipartite and d-regular.
# Cost: number of unordered vertex pairs at distance > D, computed with
# bit-packed reachability sets in numpy.
# Growth: remove d disjoint edges and attach one new A and one new B vertex,
# so the graph stays d-regular and only needs re-annealing.
# Only states with cost exactly 0 are recorded, so every recorded graph is valid.
# ----------------------------------------------------------------------------

_POP = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _cost(nbr, ident, N, D):
    """Unordered pairs at distance > D in the graph given by neighbour array nbr."""
    R = ident
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nbr], axis=1)
    cnt = _POP[R].sum(axis=1)
    return int((N - cnt).sum()) // 2


def _swap(adj, E, a1, b1, a2, b2):
    """Replace edges (a1,b1),(a2,b2) by (a1,b2),(a2,b1). Caller checks validity."""
    A1, B1, A2, B2 = 2 * a1, 2 * b1 + 1, 2 * a2, 2 * b2 + 1
    adj[A1][adj[A1].index(B1)] = B2
    adj[A2][adj[A2].index(B2)] = B1
    adj[B1][adj[B1].index(A1)] = A2
    adj[B2][adj[B2].index(A2)] = A1
    E.discard((a1, b1))
    E.discard((a2, b2))
    E.add((a1, b2))
    E.add((a2, b1))


def _anneal(st, D, rng, deadline, iters):
    """Simulated annealing on double-edge swaps. Returns True when cost reaches 0."""
    m, d, adj, E = st["m"], st["d"], st["adj"], st["E"]
    N = 2 * m
    nbr = np.array(adj, dtype=np.int64)
    ident = np.packbits(np.eye(N, dtype=np.uint8), axis=1)
    cur = _cost(nbr, ident, N, D)
    T = 1.0
    for it in range(iters):
        if cur == 0:
            return True
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = max(0.08, T * 0.998)
        a1 = rng.randrange(m)
        b1 = (adj[2 * a1][rng.randrange(d)] - 1) // 2
        a2 = rng.randrange(m)
        b2 = (adj[2 * a2][rng.randrange(d)] - 1) // 2
        if a1 == a2 or b1 == b2 or (a1, b2) in E or (a2, b1) in E:
            continue
        _swap(adj, E, a1, b1, a2, b2)
        for v in (2 * a1, 2 * b1 + 1, 2 * a2, 2 * b2 + 1):
            nbr[v] = adj[v]
        new = _cost(nbr, ident, N, D)
        limit = cur - T * math.log(1.0 - rng.random())
        if new <= limit:
            cur = new
        else:
            _swap(adj, E, a1, b2, a2, b1)
            for v in (2 * a1, 2 * b1 + 1, 2 * a2, 2 * b2 + 1):
                nbr[v] = adj[v]
    return cur == 0


def _grow(st, rng):
    """Add one A and one B vertex, rewiring d disjoint edges. Returns False on failure."""
    m, d, adj, E = st["m"], st["d"], st["adj"], st["E"]
    pairs = None
    for _ in range(200):
        order = list(range(m))
        rng.shuffle(order)
        used = set()
        cur = []
        for a in order:
            if len(cur) == d:
                break
            opts = [(adj[2 * a][j] - 1) // 2 for j in range(d)]
            rng.shuffle(opts)
            for b in opts:
                if b not in used:
                    used.add(b)
                    cur.append((a, b))
                    break
        if len(cur) == d:
            pairs = cur
            break
    if pairs is None:
        return False
    na, nb = 2 * m, 2 * m + 1
    new_a, new_b = m, m
    for a, b in pairs:
        A, B = 2 * a, 2 * b + 1
        adj[A][adj[A].index(B)] = nb
        adj[B][adj[B].index(A)] = na
        E.discard((a, b))
        E.add((a, new_b))
        E.add((new_a, b))
    adj.append([2 * b + 1 for _, b in pairs])
    adj.append([2 * a for a, _ in pairs])
    st["m"] = m + 1
    return True


def _lift_family(d, D, deadline, rng, target):
    """Grow a d-regular bipartite graph one vertex pair at a time. Returns last valid (n, edges)."""
    m = d
    adj = [None] * (2 * m)
    for a in range(m):
        adj[2 * a] = [2 * b + 1 for b in range(m)]
    for b in range(m):
        adj[2 * b + 1] = [2 * a for a in range(m)]
    E = {(a, b) for a in range(m) for b in range(m)}
    st = {"m": m, "d": d, "adj": adj, "E": E}

    best = None
    while time.monotonic() < deadline:
        if _anneal(st, D, rng, deadline, 3000):
            mm = st["m"]
            best = (2 * mm, [(2 * a, 2 * b + 1) for a, b in st["E"]])
            if 2 * mm >= target:
                break
            if not _grow(st, rng):
                break
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    target = lib.moore_bound(d, D)
    rng = random.Random(seed)

    try:
        cands = []
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                cands.append(pg)
            ar = _araujo(d)
            if ar is not None:
                cands.append(ar)
        for n, e in cands:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)

        # Calibration cases already at the Moore bound return immediately.
        if best[0] < target:
            res = _lift_family(d, D, deadline, rng, target)
            if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                best = res
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
