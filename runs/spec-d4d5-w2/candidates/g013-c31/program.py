"""Construction program for bipartite graphs with max degree d and diameter <= D.

Pipeline (each stage only ever replaces the incumbent with a graph that passes lib.is_valid):
  1. Closed-form bases: projective plane (D = 3), generalized quadrangle W(q) (D >= 4).
  2. For D >= 5, a bi-Cayley voltage-lift annealing search over semidirect products.
  3. A new, unstructured family: 'swap search'. Start from a d-regular bipartite
     circulant on 2h vertices and run simulated annealing with degree-preserving
     double-edge swaps. The cost is the number of ordered pairs at distance > D,
     computed with big-int bitsets. The order is increased one step at a time.
Any failure falls back to K_{d,d}, which is valid for every D >= 2.
"""
import itertools
import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Closed-form bases
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 9 for speed)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley voltage lifts over semidirect products (annealed)
# ----------------------------------------------------------------------------

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


def _lift_cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
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


def _lift_edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal_lift(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _lift_cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _lift_edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Swap search: degree-preserving double-edge swaps on a bipartite graph
# ----------------------------------------------------------------------------

def _swap_cost(N, E, D):
    """Ordered pairs at distance > D (unreachable counts). Zero iff the graph has diameter <= D."""
    adj = [[] for _ in range(N)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    reach = [1 << v for v in range(N)]
    for _ in range(D):
        new = []
        for v in range(N):
            x = reach[v]
            for u in adj[v]:
                x |= reach[u]
            new.append(x)
        if new == reach:
            break
        reach = new
    return sum(N - r.bit_count() for r in reach)


def _swap_search(d, D, h, rng, deadline):
    """Anneal a d-regular bipartite graph on sides of size h. Returns (n, edges) or None.

    Side A is vertices 0..h-1, side B is h..2h-1. A double-edge swap replaces
    (a1,b1),(a2,b2) by (a1,b2),(a2,b1). This keeps all degrees and bipartiteness.
    """
    N = 2 * h
    E = [(a, h + (a + s) % h) for a in range(h) for s in range(d)]  # distinct when h >= d
    S = set(E)
    m = len(E)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    def attempt(i, j):
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return None
        n1 = (a1, b2)
        n2 = (a2, b1)
        if n1 in S or n2 in S:
            return None
        return n1, n2

    def apply(i, j, n1, n2):
        S.discard(E[i])
        S.discard(E[j])
        S.add(n1)
        S.add(n2)
        E[i] = n1
        E[j] = n2

    # Mix the initial circulant so it is no longer structured.
    for _ in range(4 * m):
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        r = attempt(i, j)
        if r is not None:
            apply(i, j, *r)

    cost = _swap_cost(N, E, D)
    best_cost = cost
    best_E = list(E)
    T0, T1 = 2.0, 0.05
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        r = attempt(i, j)
        if r is None:
            continue
        old1, old2 = E[i], E[j]
        apply(i, j, *r)
        c2 = _swap_cost(N, E, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_E = list(E)
        else:
            apply(i, j, old1, old2)

    if best_cost == 0:
        return N, best_E
    return None


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def _fallback(d):
    """K_{d,d}: diameter 2, valid for every D >= 2."""
    return lib.haar_graph(d, range(d))


def _build(d, D, seed, start, budget, rng):
    deadline_all = start + budget
    best = _fallback(d)
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Calibration fast path: projective plane meets the Moore bound.
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 2:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Stage 2: lift annealing (D >= 5 only).
    lift_frac = 0.45 if D >= 5 else 0.0
    lift_deadline = start + lift_frac * budget
    if D >= 5:
        ks = [1, 1, 2, 2, 3, 4]
        while time.monotonic() < lift_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, 3))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal_lift(d, D, k, order, mul, rng, lift_deadline, 1500)
            if res is not None:
                consider(res[0], res[1])

    # Stage 3: swap search, growing the order one step at a time above the incumbent.
    while time.monotonic() < deadline_all - 0.5:
        h = max(d, best_n // 2 + 1)
        remaining = deadline_all - time.monotonic()
        attempt_deadline = time.monotonic() + 0.5 * remaining
        res = _swap_search(d, D, h, rng, attempt_deadline)
        if res is None:
            break
        consider(res[0], res[1])

    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    budget = 0.85 * time_limit
    rng = random.Random(seed)
    try:
        n, edges = _build(d, D, seed, start, budget, rng)
        if lib.is_valid(n, edges, d, D):
            return n, edges
    except Exception:
        pass
    n, edges = _fallback(d)
    return n, edges
