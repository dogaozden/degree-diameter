import math
import random
import time

import lib


# Bold change: for D >= 3 the main search is now a tabu search over bi-Cayley
# lifts Z_G-by-Z_k2 (semidirect products) with k base vertices per side.
# Each lift is scored by bounded BFS from one representative per side, since the
# group acts regularly on each fibre. Moves are voltage re-rolls and
# within-layer target swaps, chosen from sampled neighbourhoods with a short
# tabu list. Group order is steered upward from the current best, so every
# success raises the bar. Small baselines (projective plane, Araujo-Pardo-Lopez)
# are kept as fallbacks and checked with lib.is_valid.

_SAFETY = 0.85


def _cycle(D):
    """Even cycle C_{2D}: bipartite, degree 2, diameter D."""
    n = 2 * D
    return n, [(i, (i + 1) % n) for i in range(n)]


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2, q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _sample_group(G, k2, rng):
    """Return (order, mul) for Z_m x| Z_k2 with m = G // k2, or None."""
    if G < 2 or G % k2:
        return None
    if k2 == 1:
        order, mul, _ = lib.semidirect_group(G, 1, 1)
        return order, mul
    m = G // k2
    if m < 2:
        return None
    rs = [1] + [rng.randrange(1, m) for _ in range(60)]
    for r in rs:
        if math.gcd(r, m) != 1 or pow(r, k2, m) != 1 % m:
            continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _lift_cost(k, G, D, darts, rp):
    """Number of (representative, vertex) pairs not reached within distance D."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        p = rp(s)
        bi = i * G
        bj = (k + j) * G
        for g in range(G):
            a = bi + g
            b = bj + p[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [i * G for i in range(k)] + [(k + j) * G for j in range(k)]:
        seen = bytearray(N)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += N - cnt
    return total


def _init(d, k, G, rng):
    """d layers, each a random matching of k A-vertices onto k B-vertices, with random voltages."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    return darts


def _tabu(d, D, k, G, mul, rng, deadline, cand_n=10, tenure=6):
    """Tabu search over darts. Returns a darts list with cost 0, or None."""
    cache = {}

    def rp(s):
        p = cache.get(s)
        if p is None:
            p = [mul(g, s) for g in range(G)]
            cache[s] = p
        return p

    darts = _init(d, k, G, rng)
    cur = _lift_cost(k, G, D, darts, rp)
    best_c, best_d = cur, [list(x) for x in darts]
    tabu = [-1] * len(darts)
    step = 0
    while cur > 0 and time.monotonic() < deadline:
        step += 1
        chosen = None
        for _ in range(cand_n):
            nd = [list(x) for x in darts]
            if k == 1 or rng.random() < 0.5:
                idx = rng.randrange(len(nd))
                s = rng.randrange(G)
                if s == nd[idx][2]:
                    continue
                nd[idx][2] = s
                touched = (idx,)
            else:
                L = rng.randrange(d)
                a, b = rng.sample(range(k), 2)
                ia, ib = L * k + a, L * k + b
                nd[ia][1], nd[ib][1] = nd[ib][1], nd[ia][1]
                touched = (ia, ib)
            c = _lift_cost(k, G, D, nd, rp)
            is_tabu = any(tabu[t] > step for t in touched)
            if is_tabu and c >= best_c:
                continue
            if chosen is None or c < chosen[0]:
                chosen = (c, nd, touched)
        if chosen is None:
            continue
        cur, darts, touched = chosen
        for t in touched:
            tabu[t] = step + tenure
        if cur < best_c:
            best_c = cur
            best_d = [list(x) for x in darts]
    return best_d if best_c == 0 else None


def _edges(k, G, darts, mul):
    """Full lift: A_{i,g} ~ B_{j, g*s} for every dart (i, j, s)."""
    E = set()
    for i, j, s in darts:
        for g in range(G):
            E.add((i * G + g, (k + j) * G + mul(g, s)))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + _SAFETY * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n, e = _cycle(D)
        if lib.is_valid(n, e, d, D):
            return n, e
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
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
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    slice_len = max(1.5, 0.08 * time_limit)
    ks = [1, 1, 1, 2, 3]
    while time.monotonic() < deadline:
        if best_n >= lib.moore_bound(d, D):
            break
        k = rng.choice(ks)
        lo = max(4, best_n // (2 * k) + 1)
        G = rng.randint(lo, lo + 10)
        divs = [t for t in range(1, 13) if G % t == 0]
        k2 = rng.choice(divs)
        g = _sample_group(G, k2, rng)
        if g is None:
            continue
        order, mul = g
        slice_end = min(deadline, time.monotonic() + slice_len)
        darts = _tabu(d, D, k, order, mul, rng, slice_end)
        if darts is not None:
            n, e = _edges(k, order, darts, mul)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
