import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized local search for diameter-D bipartite graphs.
#
# Strategy:
#   1. Seed with the best known algebraic construction: the Araujo-Pardo and
#      Lopez graph for d-2 a prime power (D = 3), or the incidence graph of
#      PG(2, q) for the largest prime power q <= d-1. Keep K_{d,d} as fallback.
#   2. Grow the graph one vertex at a time. The new vertex takes d neighbours on
#      the opposite side. Each full neighbour gives up one edge to make room.
#      Then a repair search (random edge swaps, accepted when the number of
#      pairs at distance > D does not increase) tries to restore diameter D.
#   3. Every returned graph is verified with lib.is_valid. Any failure falls
#      back to the last verified graph, or to K_{d,d}.
# ----------------------------------------------------------------------------


def _key(a, b):
    return (a, b) if a < b else (b, a)


def _degrees(n, E):
    deg = [0] * n
    for u, v in E:
        deg[u] += 1
        deg[v] += 1
    return deg


def _colour(n, E):
    adj = [[] for _ in range(n)]
    for u, v in E:
        adj[u].append(v)
        adj[v].append(u)
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _saturate(n, E, d, col, rng):
    """Add random legal edges between deficient opposite-side vertices (in place)."""
    deg = _degrees(n, E)
    A = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    B = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in A for b in B if _key(a, b) not in E]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            E.add(_key(a, b))
            deg[a] += 1
            deg[b] += 1


def _cost(n, E, D):
    return lib.bad_pairs(n, list(E), D)


def _repair(n, E, d, D, col, deadline, rng, moves):
    """Random edge swaps that never increase the number of bad pairs. Edits E in place."""
    cost = _cost(n, E, D)
    while cost > 0 and moves > 0 and time.monotonic() < deadline:
        moves -= 1
        e = rng.choice(list(E))
        E.remove(e)
        deg = _degrees(n, E)
        A = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        f = None
        if A and B:
            for _ in range(200):
                a = rng.choice(A)
                b = rng.choice(B)
                k = _key(a, b)
                if k != e and k not in E:
                    f = k
                    break
        if f is None:
            E.add(e)
            continue
        E.add(f)
        c2 = _cost(n, E, D)
        if c2 <= cost:
            cost = c2
        else:
            E.remove(f)
            E.add(e)
    return cost == 0


def _grow_once(n, E, col, d, D, deadline, rng, moves):
    """Try to add one vertex and repair. Returns (n+1, E2, col2) on success, else None."""
    c = rng.randrange(2)
    E2 = set(E)
    col2 = col + [c]
    x = n
    deg = _degrees(n + 1, E2)
    opp = [v for v in range(n) if col[v] == 1 - c]
    if not opp:
        return None
    nb = rng.sample(opp, min(d, len(opp)))
    for b in nb:
        if deg[b] >= d:
            inc = [e for e in E2 if b in e]
            if not inc:
                return None
            e = rng.choice(inc)
            E2.remove(e)
            deg[e[0]] -= 1
            deg[e[1]] -= 1
    for b in nb:
        E2.add(_key(x, b))
        deg[b] += 1
    _saturate(n + 1, E2, d, col2, rng)
    if _repair(n + 1, E2, d, D, col2, deadline, rng, moves):
        return n + 1, E2, col2
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if D <= 0 or d <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best = (fb_n, list(fb_e))

    if D >= 3:
        cands = []
        # Araujo-Pardo and Lopez record family for d = q + 2 with q a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        # Incidence graph of PG(2, q), largest prime power q <= d - 1.
        for q in range(min(d - 1, 31), 1, -1):
            if lib.is_prime_power(q):
                try:
                    cands.append(lib.projective_plane_incidence(q))
                except Exception:
                    pass
                break
        for n_c, e_c in cands:
            if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
                best = (n_c, list(e_c))

        # Local growth search from the best seed.
        n = best[0]
        E = set(_key(u, v) for u, v in best[1])
        col = _colour(n, E)
        _saturate(n, E, d, col, rng)
        el = sorted(E)
        if lib.is_valid(n, el, d, D):
            best = (n, el)

        while time.monotonic() < deadline:
            res = _grow_once(n, E, col, d, D, deadline, rng, 300)
            if res is None:
                continue
            n, E, col = res
            el = sorted(E)
            if lib.is_valid(n, el, d, D):
                best = (n, el)
            else:
                break

    if not lib.is_valid(best[0], best[1], d, D):
        best = (fb_n, list(fb_e))
    return best
