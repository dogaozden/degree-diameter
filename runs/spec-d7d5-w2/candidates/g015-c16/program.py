import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact / safe families (unchanged from the parent for D = 3 and D = 4).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# NEW construction: degree-preserving edge-switch annealing on a bipartite graph.
#
# Start from a random Haar-type d-regular bipartite graph on N vertices
# (A_i ~ B_{i+t} for d distinct shifts t). Then repeatedly apply bipartite
# double-edge switches (a1-b1, a2-b2) -> (a1-b2, a2-b1). Degrees stay exactly d
# and the graph stays bipartite. The cost is the number of ordered pairs
# (u, v) at distance > D, computed with packed bitsets in numpy. Simulated
# annealing accepts or rejects each switch.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _cost(nbr, N, D):
    """Number of ordered vertex pairs at distance > D, via packed-bit reachability sets."""
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N)
    reach[idx, idx >> 6] = np.uint64(1) << (idx & 63).astype(np.uint64)
    for _ in range(D):
        gathered = reach[nbr]                       # (N, d, W)
        new = reach | np.bitwise_or.reduce(gathered, axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return N * N - total


def _swap(adj, nb, nbr, a1, b1, a2, b2):
    """Replace edges a1-b1, a2-b2 by a1-b2, a2-b1 (A-side a's, B-side b's)."""
    for x, old, new in ((a1, b1, b2), (b1, a1, a2), (a2, b2, b1), (b2, a2, a1)):
        k = adj[x].index(old)
        adj[x][k] = new
        nbr[x, k] = new
        nb[x].discard(old)
        nb[x].add(new)


def _anneal(d, D, N, rng, deadline, T0=2.0):
    """Anneal a d-regular bipartite graph on N vertices. Returns (N, edges) or None."""
    s = N // 2
    shifts = rng.sample(range(s), d)
    adj = [[] for _ in range(N)]
    for i in range(s):
        for t in shifts:
            j = s + (i + t) % s
            adj[i].append(j)
            adj[j].append(i)
    nb = [set(x) for x in adj]
    nbr = np.array(adj, dtype=np.int64)

    cost = _cost(nbr, N, D)
    best_cost = cost
    best_adj = [list(x) for x in adj]
    t_start = time.monotonic()
    span = max(1e-3, deadline - t_start)

    while cost > 0 and time.monotonic() < deadline:
        frac = (time.monotonic() - t_start) / span
        T = max(0.05, T0 * (1.0 - frac))
        a1 = rng.randrange(s)
        a2 = rng.randrange(s)
        if a1 == a2:
            continue
        b1 = adj[a1][rng.randrange(d)]
        b2 = adj[a2][rng.randrange(d)]
        if b1 == b2 or b2 in nb[a1] or b1 in nb[a2]:
            continue

        _swap(adj, nb, nbr, a1, b1, a2, b2)
        c2 = _cost(nbr, N, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_adj = [list(x) for x in adj]
        else:
            _swap(adj, nb, nbr, a1, b2, a2, b1)  # revert

    if best_cost != 0:
        return None
    edges = [(a, b) for a in range(s) for b in best_adj[a]]
    return N, edges


def _targets(d, D):
    """Descending candidate orders (even) for the annealer, as fractions of the Moore bound."""
    moore = lib.moore_bound(d, D)
    out = []
    for frac in (0.3675, 0.366, 0.364, 0.36):
        t = int(frac * moore)
        t -= t % 2
        if t >= 2 * d and t not in out:
            out.append(t)
    return out


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions for D = 3 and D = 4.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # New route for D >= 5: annealing over bipartite edge switches.
    if D >= 5 and d >= 3:
        for N in _targets(d, D):
            if N <= best_n or N > 6000:
                continue
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            slice_end = time.monotonic() + 0.5 * remaining
            try:
                res = _anneal(d, D, N, rng, slice_end)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])
                if best_n >= N:
                    break

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
