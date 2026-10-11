import math
import random
import time

import lib

_BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Baselines: projective plane incidence (diameter 3), Araujo-Pardo-Lopez (D = 3),
# and K_{d,d} / K_2 as the always-valid fallback.
# ----------------------------------------------------------------------------

def _pg_baseline(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez record graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New family for D >= 5: bi-Cayley lifts over a RANDOM finite group of order G,
# where the group is either a semidirect product Z_m x| Z_k2 or an abelian
# product Z_a x Z_b. The base graph has k A-vertices and k B-vertices, with d
# layers; layer L is a permutation p_L of range(k) giving darts (i, p_L[i], s).
# Every A and every B vertex then has degree exactly d.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for every g in the group.
# Left translation by a group element is an automorphism, so distances from the
# identity representatives of each side determine the diameter.
# ----------------------------------------------------------------------------

def _abelian(a, b):
    """Return (order, mul) for Z_a x Z_b, element x coded as x1*b + x2."""
    def mul(x, y):
        x1, x2 = divmod(x, b)
        y1, y2 = divmod(y, b)
        return ((x1 + y1) % a) * b + (x2 + y2) % b
    return a * b, mul


def _sample_group(G, rng):
    """Return (order, mul) for a random group of order G, or None."""
    k2s = [k2 for k2 in range(1, 13) if G % k2 == 0 and G // k2 >= 2]
    if not k2s:
        return None
    if rng.random() < 0.4:
        divs = [a for a in range(2, G) if G % a == 0 and G // a >= 2]
        if divs:
            a = rng.choice(divs)
            return _abelian(a, G // a)
    k2 = rng.choice(k2s)
    m = G // k2
    if k2 == 1:
        order, mul, _ = lib.cyclic_group(m)
        return order, mul
    rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
    if not rs:
        return None
    r = rng.choice(rs)
    try:
        order, mul, _ = lib.semidirect_group(m, k2, r)
    except ValueError:
        return None
    return order, mul


def _perm_cache(mul, G):
    """Return perm(s): the list g -> mul(g, s), cached per s."""
    cache = {}

    def perm(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    return perm


def _cost(k, G, D, darts, perms, limit=float("inf")):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
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
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = []
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.append((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, E


def _anneal(d, D, k, G, mul, rng, deadline, start=None, T0=1.0):
    """Simulated annealing over voltages and layer permutations.

    Returns (graph_or_None, darts, cost) where graph_or_None = (n, edges) on success.
    """
    perm = _perm_cache(mul, G)
    if start is None:
        darts = []
        for _ in range(d):
            p = rng.sample(range(k), k)
            for i in range(k):
                darts.append([i, p[i], rng.randrange(G)])
    else:
        darts = [list(x) for x in start]
    perms = [perm(s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    best_cost = cost
    best_darts = [list(x) for x in darts]
    T = T0
    while cost > 0 and time.monotonic() < deadline:
        T = max(0.05, T * 0.998)
        limit = cost - T * math.log(1.0 - rng.random())
        idx = rng.randrange(len(darts))
        if k == 1 or rng.random() < 0.6:
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_p = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = perm(new_s)
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
                continue
        else:
            L, a = divmod(idx, k)
            b = rng.randrange(k)
            if b == a:
                continue
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
                continue
        if cost < best_cost:
            best_cost = cost
            best_darts = [list(x) for x in darts]
    if cost == 0:
        N, E = _edges(k, G, darts, perms)
        return (N, E), darts, 0
    return None, best_darts, best_cost


def _perturb(st, G, rng):
    out = [list(x) for x in st]
    for _ in range(rng.randint(1, 3)):
        out[rng.randrange(len(out))][2] = rng.randrange(G)
    return out


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Always-valid fallback: K_{d,d} (diameter 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_baseline(d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                consider(ar[0], ar[1])

    # Calibration cases already at the Moore bound return immediately.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: bi-Cayley lifts over random groups with annealing,
    # warm restarts from elite near-misses, and growing order.
    KS = [1, 1, 2, 2, 2, 3, 3, 4, 5]
    elite = {}  # (k, order) -> (cost, darts)
    while time.monotonic() < deadline:
        k = rng.choice(KS)
        lo = max(2, best_n // (2 * k) + 1)
        G = rng.randint(lo, lo + max(2, lo // 25))
        g = _sample_group(G, rng)
        if g is None:
            continue
        order, mul = g
        key = (k, order)

        start_state = None
        if key in elite and rng.random() < 0.5:
            start_state = _perturb(elite[key][1], order, rng)

        att_deadline = min(deadline, time.monotonic() + 4.0)
        res, st, c = _anneal(d, D, k, order, mul, rng, att_deadline, start_state)
        if res is not None:
            consider(res[0], res[1])
        elif key not in elite or c < elite[key][0]:
            elite[key] = (c, st)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
