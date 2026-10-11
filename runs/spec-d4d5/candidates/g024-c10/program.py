import math
import random
import time

import lib


_DUP_PEN = 10 ** 6
_GROUP_CACHE = {}


def _divisors(G):
    return [a for a in range(1, G + 1) if G % a == 0]


def _group_table(a, b):
    """Addition table of the abelian group Z_a x Z_b, element (u, v) coded as u*b + v."""
    key = (a, b)
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    if len(_GROUP_CACHE) > 40:
        _GROUP_CACHE.clear()
    G = a * b
    tab = []
    for x in range(G):
        u1, v1 = divmod(x, b)
        row = [0] * G
        for y in range(G):
            u2, v2 = divmod(y, b)
            row[y] = ((u1 + u2) % a) * b + (v1 + v2) % b
        tab.append(row)
    _GROUP_CACHE[key] = tab
    return tab


def _adjacency(k, G, tab, darts):
    """Adjacency lists of the bi-lift. Dart (i, j, s) joins A(i,g) to B(j, g+s) for all g."""
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        ab = i * G
        bb = (k + j) * G
        for g in range(G):
            x = ab + g
            y = bb + tab[g][s]
            adj[x].append(y)
            adj[y].append(x)
    return adj


def _cost(k, G, D, tab, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D.

    Translations by group elements are automorphisms of the lift, so one representative
    per layer suffices.
    """
    dup = len(darts) - len({(i, j, s) for i, j, s in darts})
    if dup:
        return _DUP_PEN * dup
    N = 2 * k * G
    adj = _adjacency(k, G, tab, darts)
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
    return total


def _to_edges(k, G, tab, darts):
    E = []
    for i, j, s in darts:
        for g in range(G):
            E.append((i * G + g, (k + j) * G + tab[g][s]))
    return 2 * k * G, E


def _anneal(d, D, k, G, tab, rng, deadline, iters):
    """Simulated annealing over voltages and per-slot target permutations.

    Each slot L holds a permutation p_L of range(k); darts (i, p_L(i), s) give every
    A-layer and every B-layer exactly d incident darts, so the lift is d-regular.
    Returns the dart list if the diameter bound holds, else None.
    """
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, tab, darts)
    T0 = max(1.0, 0.03 * cost) if cost < 10 ** 5 else 5.0
    T1 = 0.3

    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / max(1, iters))
        if k == 1 or rng.random() < 0.6:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, tab, darts)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            x, y = rng.sample(range(k), 2)
            ia, ib = L * k + x, L * k + y
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, tab, darts)
            if c2 <= cost or rng.random() < math.exp((cost - c2) / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return darts
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        # Even cycle of length 2D: bipartite, 2-regular, diameter D (Moore bound).
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Safe fallback: K_{d,d}, diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    q = d - 1
    if lib.is_prime_power(q):
        # Incidence graph of PG(2, q): diameter 3 and degree q+1 = d, meets the Moore bound.
        n, e = lib.projective_plane_incidence(q)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
        if D == 3:
            return best  # optimal for D = 3: return immediately

    best_n = best[0]

    # Main search: annealed bi-lifts over abelian (possibly non-cyclic) groups Z_a x Z_b,
    # with one or more base vertices per side. The group order is chosen so that each
    # accepted lift strictly exceeds the current best order.
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3))
        base = best_n // (2 * k)
        G = max(2, base + 1 + rng.randrange(0, 3))
        a = rng.choice(_divisors(G))
        b = G // a
        tab = _group_table(a, b)
        darts = _anneal(d, D, k, G, tab, rng, deadline, iters=2500)
        if darts is not None:
            n, e = _to_edges(k, G, tab, darts)
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
