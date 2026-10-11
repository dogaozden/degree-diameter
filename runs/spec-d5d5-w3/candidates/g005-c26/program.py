import math
import random
import time

import lib

_BIG = 10 ** 9
_RCACHE = {}


def _pg_best(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _rtable(m, k, r):
    """Cached (order, R) with R[s][g] = g * s in Z_m x|_r Z_k."""
    key = (m, k, r)
    hit = _RCACHE.get(key)
    if hit is not None:
        return hit
    if len(_RCACHE) > 64:
        _RCACHE.clear()
    order, mul, _ = lib.semidirect_group(m, k, r)
    R = [[mul(g, s) for g in range(order)] for s in range(order)]
    _RCACHE[key] = (order, R)
    return _RCACHE[key]


def _cost(k, G, D, darts, R):
    """Number of (representative, vertex) pairs not within distance D. Zero means valid.

    Vertices: A_{i,x} = i*G + x and B_{j,y} = (k+j)*G + y. Dart (i, j, s) joins
    A_{i,x} to B_{j,x*s}. Left translation is an automorphism, so one representative
    per base vertex on each side suffices.
    """
    seen_keys = set()
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        key = (i, j, s)
        if key in seen_keys:
            return _BIG
        seen_keys.add(key)
        Rs = R[s]
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + Rs[g]
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


def _anneal(d, D, k, G, R, rng, deadline, iters):
    """Annealing over voltages and layered base matchings; each layer is a permutation of k."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, R)
    T = 1.5
    T_end = 0.2
    decay = (T_end / T) ** (1.0 / max(1, iters))

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T *= decay
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, R)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost != 0:
        return None
    E = set()
    for i, j, s in darts:
        Rs = R[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + Rs[g]))
    return 2 * k * G, sorted(E)


def _search(d, D, box, rng, deadline, moore):
    """Grow box[0] by repeated multi-base voltage lifts over semidirect products."""
    while time.monotonic() < deadline:
        best_n = box[0][0]
        if best_n >= moore:
            break
        k = rng.choice((1, 2, 2, 3, 3, 4))
        G = best_n // (2 * k) + 1 + rng.randrange(3)
        if 2 * k * G > moore:
            G = moore // (2 * k)
        if G < 2 or 2 * k * G <= best_n:
            continue
        groups = _groups(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, R = _rtable(m, k2, r)
        res = _anneal(d, D, k, order, R, rng, deadline, 2500)
        if res is not None and res[0] > best_n and lib.is_valid(res[0], res[1], d, D):
            box[0] = res


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    best = fallback
    moore = lib.moore_bound(d, D)

    try:
        if D == 3:
            pg = _pg_best(d)
            if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
                best = pg
        else:
            box = [best]
            _search(d, D, box, rng, deadline, moore)
            best = box[0]
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
