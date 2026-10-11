import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) incidence graph (D = 4 base).
# ----------------------------------------------------------------------------

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
    color = [0] * P + [1] * len(lines)
    return P + len(lines), edges, color


def _saturate(n, edges, d, color, rng):
    """Add edges between opposite sides while both endpoints have spare degree."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Haar graphs over groups: A_x ~ B_{x*s} for s in S (|S| = d). Both sides are
# d-regular and the graph is bipartite by construction.
# ----------------------------------------------------------------------------

def _haar(order, mul, S):
    edges = [(x, order + mul(x, s)) for x in range(order) for s in S]
    return 2 * order, edges


def _groups(lo, hi, rng):
    """(N, m, k, r) for semidirect groups Z_m x| Z_k of order N in [lo, hi], largest N first."""
    out = []
    for N in range(hi, lo - 1, -1):
        for k in range(1, 9):
            if N % k:
                continue
            m = N // k
            if m < 2:
                continue
            rs = [r for r in range(1, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            other = [r for r in rs if r != 1]
            rng.shuffle(other)
            for r in [1] + other[:2]:
                out.append((N, m, k, r))
    return out


def _local_search(order, mul, d, D, deadline, rng):
    """Minimise bad pairs over connection sets S of size d; restart on stagnation."""
    while time.monotonic() < deadline:
        S = rng.sample(range(order), d)
        n, e = _haar(order, mul, S)
        cost = lib.bad_pairs(n, e, D)
        stale = 0
        while cost > 0 and stale < 300 and time.monotonic() < deadline:
            i = rng.randrange(d)
            x = rng.randrange(order)
            if x in S:
                stale += 1
                continue
            T = S[:]
            T[i] = x
            n2, e2 = _haar(order, mul, T)
            c2 = lib.bad_pairs(n2, e2, D)
            if c2 <= cost:
                stale = 0 if c2 < cost else stale + 1
                S, cost = T, c2
            else:
                stale += 1
        if cost == 0:
            return S
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + max(1.0, min(0.8 * T, T - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        if D >= 2:
            consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best
    if D == 2:
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    # Algebraic bases.
    if D == 3 and lib.is_prime_power(d - 1):
        n0, e0 = lib.projective_plane_incidence(d - 1)
        m0 = n0 // 2
        color = [0] * m0 + [1] * m0
        consider(n0, _saturate(n0, e0, d, color, rng))
    elif D == 4:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)]
        if qs:
            try:
                n0, e0, color = _gq_w(qs[0])
                consider(n0, _saturate(n0, e0, d, color, rng))
            except Exception:
                pass

    # Group-Haar search: look for a connection set of size d giving diameter D
    # on a group of order N, trying the largest orders first.
    hi = moore // 2
    lo = best[0] // 2 + 1
    if lo <= hi and time.monotonic() < deadline:
        try:
            for N, m, k, r in _groups(lo, hi, rng):
                now = time.monotonic()
                if now >= deadline:
                    break
                budget = max(0.5, 0.15 * (deadline - now))
                order, mul, _ = lib.semidirect_group(m, k, r)
                S = _local_search(order, mul, d, D, min(deadline, now + budget), rng)
                if S is not None:
                    n, e = _haar(order, mul, S)
                    consider(n, e)
                    break
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
