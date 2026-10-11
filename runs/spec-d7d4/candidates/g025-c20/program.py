import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline: incidence graph of the generalized quadrangle W(q) (diameter 4).
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of W(q); order 2(q+1)(q^2+1), degree q+1, diameter 4."""
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


# ----------------------------------------------------------------------------
# New construction: regular bipartite graphs with N + N vertices, degree d,
# found by simulated annealing over double-edge switches. The cost is the number
# of vertex pairs at distance > D (bitset balls). Diameter D is reached when the
# cost hits zero. Unlike voltage lifts, this search has no group structure.
# ----------------------------------------------------------------------------

def _balls_cost(N2, adj, D):
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
    ball = [1 << v for v in range(N2)]
    for _ in range(D):
        new = [0] * N2
        for v in range(N2):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new[v] = x
        ball = new
    return sum(N2 - b.bit_count() for b in ball) // 2


def _make_adj(N, E):
    N2 = 2 * N
    adj = [[] for _ in range(N2)]
    for a, b in E:
        adj[a].append(N + b)
        adj[N + b].append(a)
    return adj


def _anneal(N, d, D, rng, deadline):
    """Search a d-regular bipartite graph on N+N vertices with diameter <= D.

    Returns the list of (a, b) pairs (b indexes the second side), or None.
    """
    if N < d:
        return None
    N2 = 2 * N
    E = []
    S = set()
    for i in range(N):
        for s in range(d):
            b = (i + s) % N
            E.append((i, b))
            S.add((i, b))
    adj = _make_adj(N, E)
    cost = _balls_cost(N2, adj, D)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = 2.0 * (0.03 ** frac)
        # Random double-edge switch preserving regularity and simplicity.
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in S or (a2, b1) in S:
            continue
        E[i] = (a1, b2)
        E[j] = (a2, b1)
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        nadj = _make_adj(N, E)
        c2 = _balls_cost(N2, nadj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            adj = nadj
        else:
            E[i] = (a1, b1)
            E[j] = (a2, b2)
            S.discard((a1, b2))
            S.discard((a2, b1))
            S.add((a1, b1))
            S.add((a2, b2))
    if cost == 0:
        return list(E)
    return None


# ----------------------------------------------------------------------------
# Driver.
# 1. Safe baselines (K_{d,d}, cycle for d=2, projective plane or W(q) when they fit).
# 2. Annealing search for regular bipartite graphs, growing the side size N
#    one step at a time from the best baseline.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, 0.8 * time_limit - 2.0)
    deadline = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    # Baselines from known structures.
    try:
        if D == 3:
            for q in range(d - 1, 1, -1):
                if lib.is_prime_power(q):
                    consider(*lib.projective_plane_incidence(q))
                    break
        elif D >= 4:
            for q in range(min(d - 1, 7), 1, -1):
                if lib.is_prime_power(q) and q + 1 <= d:
                    consider(*_gq_w(q))
                    break
    except Exception:
        pass

    # Stop early if the baseline already meets the Moore bound.
    if best[0] >= lib._moore_bound(d, D):
        return best

    # Annealing: grow the side size N from the current best.
    try:
        N_t = max(d, best[0] // 2 + 1)
        while time.monotonic() < deadline - 0.5:
            remaining = deadline - time.monotonic()
            attempt_end = min(deadline, time.monotonic() + max(2.0, 0.3 * remaining))
            E = _anneal(N_t, d, D, rng, attempt_end)
            if E is not None:
                edges = [(a, N_t + b) for a, b in E]
                consider(2 * N_t, edges)
                N_t += 1
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
