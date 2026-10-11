import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Baseline families for D = 3 (projective plane, Araujo-Pardo-Lopez).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# NEW: symmetric Haar-graph search with a single-BFS cost.
#
# The Haar graph H(Z_m, S) has vertices a_i, b_j (i, j in Z_m) with a_i ~ b_{i+s}
# for s in S, |S| = d. Three symmetries make one BFS enough:
#   * translation a_i -> a_{i+t}, b_j -> b_{j+t} (transitive on each side);
#   * the swap a_x -> b_{-x}, b_y -> a_{-y} (an automorphism, since S = -S + ... is
#     handled by the same identity a_x ~ b_{x+s} <-> b_{-x} ~ a_{-x-s}).
# So a pair of vertices is at distance <= D iff its translate-and-swap image
# involving a_0 is, and it suffices that a_0 reaches all 2m vertices within D.
# The cost is therefore the number of vertices missed by one BFS from a_0.
# An adaptive ladder grows m (geometric steps, halved on failure) and
# simulated annealing repairs S for each m.
# ----------------------------------------------------------------------------

def _haar_unreached(m, S, D):
    """Number of vertices of H(Z_m, S) at distance > D from a_0. Zero means valid."""
    seen_a = bytearray(m)
    seen_b = bytearray(m)
    seen_a[0] = 1
    fa = [0]
    fb = []
    reached = 1
    for step in range(D):
        nf = []
        if step % 2 == 0:
            for x in fa:
                for s in S:
                    y = (x + s) % m
                    if not seen_b[y]:
                        seen_b[y] = 1
                        nf.append(y)
            fb = nf
        else:
            for y in fb:
                for s in S:
                    x = (y - s) % m
                    if not seen_a[x]:
                        seen_a[x] = 1
                        nf.append(x)
            fa = nf
        reached += len(nf)
        if not nf:
            break
    return 2 * m - reached


def _haar_search(d, D, m, rng, deadline):
    """Anneal a connection set S (|S| = d, 0 in S) in Z_m so H(Z_m, S) has diameter <= D."""
    if m < d or d < 2:
        return None
    S = [0] + rng.sample(range(1, m), d - 1)
    c = _haar_unreached(m, S, D)
    T = 2.0
    it = 0
    while c > 0:
        it += 1
        if it % 32 == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        old = S[i]
        S[i] = x
        ct = _haar_unreached(m, S, D)
        if ct <= c or rng.random() < math.exp(-(ct - c) / T):
            c = ct
        else:
            S[i] = old
        T = max(0.2, T * 0.998)
    return list(S) if c == 0 else None


def _haar_ladder(d, D, best_m, m_max, rng, end, budget, consider_haar):
    """Grow m geometrically: double the step on success, halve it on failure."""
    step = max(1, best_m // 8)
    while True:
        now = time.monotonic()
        if now >= end - 0.05 or best_m >= m_max:
            break
        m_try = min(best_m + step, m_max)
        if m_try <= best_m:
            break
        S = _haar_search(d, D, m_try, rng, min(end, now + budget))
        if S is not None and consider_haar(m_try, S):
            best_m = m_try
            step = step * 2
        else:
            step = max(1, step // 2)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over small semidirect products (k >= 2 base vertices per side).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    divs = [k2 for k2 in (1, 2, 3, 4, 6) if G % k2 == 0 and G // k2 >= 2]
    if not divs:
        return None
    k2 = rng.choice(divs)
    m = G // k2
    if k2 == 1:
        order, mul, _ = lib.semidirect_group(m, 1, 1)
        return order, mul
    cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not cands:
        return None
    r = rng.choice(cands)
    order, mul, _ = lib.semidirect_group(m, k2, r)
    return order, mul


def _lift_cost(k, G, D, darts, perms):
    """Vertices missed within distance D from one representative per base vertex."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            a = i * G + g
            b = (k + j) * G + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = bytearray(N)
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _lift_anneal(d, D, k, G, mul, rng, deadline):
    """Anneal voltages of a d-layer bi-Cayley lift. Returns (n, edges) or None."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(g, s) for g in range(G)] for _, _, s in darts]
    cost = _lift_cost(k, G, D, darts, perms)
    T = 1.0
    it = 0
    while cost > 0:
        it += 1
        if it % 16 == 0 and time.monotonic() > deadline:
            break
        idx = rng.randrange(len(darts))
        old_s, old_p = darts[idx][2], perms[idx]
        new_s = rng.randrange(G)
        darts[idx][2] = new_s
        perms[idx] = [mul(g, new_s) for g in range(G)]
        c2 = _lift_cost(k, G, D, darts, perms)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            darts[idx][2] = old_s
            perms[idx] = old_p
        T = max(0.2, T * 0.995)
    if cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best_n >= moore:
        return best

    end_haar = start + 0.55 * time_limit
    end_all = start + 0.8 * time_limit
    budget = max(1.0, 0.05 * time_limit)

    def consider_haar(m, S):
        n, e = lib.haar_graph(m, S)
        return consider(n, e)

    # Phase 1: Haar graph ladder (new symmetric single-BFS cost).
    _haar_ladder(d, D, best_n // 2, moore // 2, rng, end_haar, budget, consider_haar)

    # Phase 2: bi-Cayley lifts over small semidirect products.
    while time.monotonic() < end_all - 0.5 and best_n < moore:
        k = rng.choice([2, 2, 3])
        base = max(1, best_n // (2 * k))
        G = rng.randint(base + 1, base + max(3, base // 8))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        att_end = min(end_all, time.monotonic() + budget)
        res = _lift_anneal(d, D, k, order, mul, rng, att_end)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
