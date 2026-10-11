import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Small deterministic bases: projective plane (D >= 3) and Araujo-Pardo-Lopez (D = 3).
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
# Different family for D >= 4: bi-Cayley lifts with k base vertices per side over
# non-abelian groups Z_m x| Z_k2, searched by simulated annealing on the
# representative-BFS cost. Left translation by the group is an automorphism, so
# checking one representative per base orbit (A_i,e and B_j,e) is exact.
#
# Vertices: A_i,x = i*G + x and B_j,x = (k+j)*G + x.
# Dart (i, j, s): A_i,x ~ B_j, x*s for every x in the group.
# Each layer L of d layers uses a permutation of the k B-orbits, so the lift is d-regular.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _group_options(G):
    """All (m, k2, r) with m * k2 = G giving the semidirect product Z_m x| Z_k2 (r = 1 when k2 = 1)."""
    opts = []
    for k2 in range(1, min(G, 16) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            opts.append((m, 1, 1))
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                opts.append((m, k2, r))
    return opts


def _cost(k, G, D, darts, perms):
    """Total number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        bi = i * G
        bj = (k + j) * G
        for x in range(G):
            a = bi + x
            b = bj + pm[x]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in [t * G for t in range(2 * k)]:
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
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and B-endpoint swaps within layers. Returns (darts, cost)."""
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [[mul(x, s) for x in range(G)] for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.15, T * 0.997)
        idx = rng.randrange(len(darts))
        if k == 1 or rng.random() < 0.75:
            old_s = darts[idx][2]
            old_p = perms[idx]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            darts[idx][2] = new_s
            perms[idx] = [mul(x, new_s) for x in range(G)]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_p
        else:
            L = idx // k
            a = idx
            b = L * k + rng.randrange(k)
            if a == b:
                continue
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            c2 = _cost(k, G, D, darts, perms)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
    return darts, cost


def _graph_from(k, G, mul, darts):
    """Build (n, edges) of the lift defined by darts."""
    E = set()
    for i, j, s in darts:
        bi = i * G
        bj = (k + j) * G
        for x in range(G):
            E.add((bi + x, bj + mul(x, s)))
    return 2 * k * G, sorted(E)


def _store(state, d, D, n, e):
    """Keep (n, e) if it is larger than the current best and passes the exact validity check."""
    if n > state['n'] and lib.is_valid(n, e, d, D):
        state['n'] = n
        state['g'] = (n, e)


def _lift_search(d, D, rng, deadline, state):
    """Climb: repeatedly search for a valid lift strictly larger than the current best."""
    cache = {}
    while time.monotonic() < deadline and state['n'] < lib.moore_bound(d, D):
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = state['n'] // (2 * k)
        lo = max(2, base + 1)
        hi = lo + max(2, lo // 6)
        G = rng.randint(lo, hi)
        if G not in cache:
            cache[G] = _group_options(G)
        opts = cache[G]
        if not opts:
            continue
        m, k2, r = rng.choice(opts)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        run_deadline = min(deadline, time.monotonic() + 6.0)
        darts, cost = _anneal(d, D, k, order, mul, rng, run_deadline, 2500)
        if cost == 0:
            n, e = _graph_from(k, order, mul, darts)
            _store(state, d, D, n, e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    fallback = lib.haar_graph(d, range(d))
    state = {'n': fallback[0], 'g': fallback}

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                _store(state, d, D, pg[0], pg[1])
            if D == 3:
                ar = _araujo(d)
                if ar is not None:
                    _store(state, d, D, ar[0], ar[1])
        if D >= 3 and state['n'] < lib.moore_bound(d, D):
            _lift_search(d, D, rng, deadline, state)
    except Exception:
        pass

    best = state['g']
    if not lib.is_valid(best[0], best[1], d, D):
        best = fallback
    return best
