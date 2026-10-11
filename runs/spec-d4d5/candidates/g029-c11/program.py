import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Structured bases (fallbacks and starting points).
# ----------------------------------------------------------------------------

def _largest_pg_q(d):
    """Largest prime power q with q + 1 <= d, or None."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _gq_w(q):
    """Point-line incidence graph of the generalized quadrangle W(q); diameter 4, degree q + 1."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


# ----------------------------------------------------------------------------
# New main idea: edge-swap annealing on d-regular bipartite graphs.
#
# A bipartite graph on sides A = {0..N-1}, B = {0..N-1} is stored as a list E of
# pairs (a, b). Double edge swaps (a1,b1),(a2,b2) -> (a1,b2),(a2,b1) keep every
# degree equal to d and keep the graph bipartite. The cost is the number of
# unordered vertex pairs at distance more than D. We anneal the cost to zero
# at increasing N, starting from a circulant (Haar-type) d-regular graph.
# ----------------------------------------------------------------------------

def _cost(N, D, E):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    n = 2 * N
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new[v] = x
        if new == reach:
            break
        reach = new
    return (n * n - sum(r.bit_count() for r in reach)) // 2


def _anneal(N, d, D, rng, end, T0=1.5, T1=0.05):
    """Anneal a d-regular bipartite graph on 2N vertices to diameter <= D; returns E or None."""
    E = [(i, (i + s) % N) for i in range(N) for s in range(d)]
    S = set(E)
    cost = _cost(N, D, E)
    m = len(E)
    start = time.monotonic()
    span = max(1e-3, end - start)
    while cost > 0:
        now = time.monotonic()
        if now >= end:
            return None
        T = T0 * (T1 / T0) ** ((now - start) / span)
        for _ in range(20):
            i = rng.randrange(m)
            j = rng.randrange(m)
            a1, b1 = E[i]
            a2, b2 = E[j]
            if a1 == a2 or b1 == b2:
                continue
            n1 = (a1, b2)
            n2 = (a2, b1)
            if n1 in S or n2 in S:
                continue
            E[i] = n1
            E[j] = n2
            S.difference_update({(a1, b1), (a2, b2)})
            S.update({n1, n2})
            c2 = _cost(N, D, E)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
                if cost == 0:
                    break
            else:
                E[i] = (a1, b1)
                E[j] = (a2, b2)
                S.difference_update({n1, n2})
                S.update({(a1, b1), (a2, b2)})
    return E if cost == 0 else None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle C_{2D}: bipartite, degree 2, diameter D (optimal for d = 2).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        q = _largest_pg_q(d)
        if q is not None:
            consider(*lib.projective_plane_incidence(q))
            # Moore-optimal for D = 3 when d - 1 is a prime power: nothing to gain.
            if D == 3 and q == d - 1:
                return best

    if D >= 4:
        qs = [x for x in range(min(d - 1, 5), 1, -1) if lib.is_prime_power(x)]
        if qs:
            consider(*_gq_w(qs[0]))

    # Edge-swap annealing: climb N upward from a comfortable starting point.
    if D >= 3 and d >= 3:
        best_n = best[0]
        N = max(d, best_n // 2 - 8)
        attempt_len = max(1.5, 0.12 * time_limit)
        while time.monotonic() < deadline:
            now = time.monotonic()
            end = min(deadline, now + attempt_len)
            E = _anneal(N, d, D, rng, end)
            if E is not None:
                n = 2 * N
                consider(n, [(a, N + b) for a, b in E])
                N += 1
            # On failure, retry the same N from a fresh random start.

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
