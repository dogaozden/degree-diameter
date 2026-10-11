import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if d <= 0 or D <= 0:
        return 1
    if d == 1:
        return 2
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


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
# New construction: bipartite regular graph from circulant-type start, then
# double-edge swaps under simulated annealing to minimise the number of vertex
# pairs at distance > D. Each swap keeps the graph simple and d-regular, so
# the result is always bipartite with max degree d.
# ----------------------------------------------------------------------------

def _bad(n, adj, D):
    """Ordered count of vertex pairs at distance > D (zero means diameter <= D)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            nxt.append(r)
        reach = nxt
    return sum(n - r.bit_count() for r in reach)


def _swap_search(d, D, k, rng, deadline):
    """Anneal double-edge swaps on a d-regular bipartite graph with parts of size k.

    Returns a validated (n, edges) with diameter <= D, or None.
    """
    n = 2 * k
    shifts = rng.sample(range(k), d)
    E = []
    for a in range(k):
        for s in shifts:
            E.append((a, k + (a + s) % k))
    adj = [[] for _ in range(n)]
    eset = set(E)
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)

    def setE(idx, pair):
        old = E[idx]
        eset.discard(old)
        adj[old[0]].remove(old[1])
        adj[old[1]].remove(old[0])
        eset.add(pair)
        adj[pair[0]].append(pair[1])
        adj[pair[1]].append(pair[0])
        E[idx] = pair

    cost = _bad(n, adj, D)
    m = len(E)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    T0 = 1.0
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - start) / span
        T = max(0.05, T0 * (1.0 - frac))
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (a1, b2) in eset or (a2, b1) in eset:
            continue
        setE(i, (a1, b2))
        setE(j, (a2, b1))
        c2 = _bad(n, adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            setE(i, (a1, b1))
            setE(j, (a2, b2))

    if cost != 0:
        return None
    edges = [(int(u), int(v)) for u, v in E]
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _swap_driver(d, D, lo, hi, rng, deadline, consider):
    """Binary search on the side size k for which the swap search succeeds."""
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        probe_end = min(deadline, now + max(2.0, 0.45 * (deadline - now)))
        res = _swap_search(d, D, mid, rng, probe_end)
        if res is not None:
            consider(res[0], res[1])
            lo = mid
        else:
            hi = mid - 1


# ----------------------------------------------------------------------------
# Group voltage lifts (previous main search, kept as a second method).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    return [mul(g, s) for g in range(G)]


def _gcost(k, G, D, darts, perms):
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _gedges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _gsearch(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    layers = [rng.sample(range(k), k) for _ in range(d)]
    darts = []
    for p in layers:
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _gcost(k, G, D, darts, perms)

    best_cost = cost
    best_state = ([list(x) for x in darts], list(perms))

    T0, T_floor = 3.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_floor, T0 * (1.0 - it / iters))
        idx = rng.randrange(len(darts))
        old_s = darts[idx][2]
        old_perm = perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = _right_perm(mul, G, new_s)
        c2 = _gcost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_state = ([list(x) for x in darts], list(perms))
        else:
            darts[idx][2] = old_s
            perms[idx] = old_perm

    if best_cost == 0:
        darts, perms = best_state
        return _gedges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = 0.8 * time_limit
    end = start + budget
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= _moore(d, D):
        return best

    # Method 1: swap-based annealing on regular bipartite graphs (new construction).
    if d >= 3 and time.monotonic() < end:
        swap_deadline = start + 0.5 * budget
        lo = max(d, best_n // 2)
        hi = max(lo, _moore(d, D) // 2)
        _swap_driver(d, D, lo, hi, rng, swap_deadline, consider)

    # Method 2: annealed group voltage lifts with the remaining time.
    while time.monotonic() < end:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, max(3, base // 6 + 1)))
        res = _gsearch(d, D, k, G, rng, 2000, end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
