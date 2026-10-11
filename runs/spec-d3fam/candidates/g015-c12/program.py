"""Diameter-3 bipartite construction with a rewiring search for d = 11, 13, 15.

Scope: D = 2 returns K_{d,d}. D >= 3 with d-1 a prime power returns the Moore-optimal
PG(2, d-1) incidence graph. Otherwise the best valid base is the Araujo-Pardo-Lopez
graph (d-2 a prime power) or PG(2, q), and for D = 3 it is then extended by a
rewiring search. Each extension inserts one A-vertex and one B-vertex with full
degree, then anneals double-edge swaps to drive the number of pairs at distance > D
to zero. Every returned graph passes lib.is_valid. Non-target D >= 4 cases use the
simpler PG fallback only.
"""
import math
import random
import time

import lib


def _pg_candidate(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q <= d - 2."""
    for q in range(d - 2, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _sides(n, adj):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return [c if c >= 0 else 0 for c in color]


def _bad_pairs(n, E, D):
    """Number of unordered vertex pairs at distance more than D (bitmask balls)."""
    adj = [[] for _ in range(n)]
    for a, b in E:
        adj[a].append(b)
        adj[b].append(a)
    ball = [1 << v for v in range(n)]
    for v in range(n):
        for u in adj[v]:
            ball[v] |= 1 << u
    for _ in range(D - 1):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - ball[v].bit_count() for v in range(n)) // 2


def _insert_pair(n, E, S, d, rng):
    """Add an A-vertex x = n and a B-vertex y = n+1, each of degree d, by rerouting old edges.

    Edge (a, b) becomes (x, b) and (a, y). Old vertex degrees are unchanged.
    Returns the new vertex count, or None on failure.
    """
    x, y = n, n + 1
    old = n
    nb_x, nb_y = set(), set()
    tries = 0
    while len(nb_x) < d and tries < 100000:
        tries += 1
        i = rng.randrange(len(E))
        a, b = E[i]
        if a >= old or b >= old:
            continue
        if b in nb_x or a in nb_y:
            continue
        S.discard((a, b))
        E[i] = (x, b)
        S.add((x, b))
        E.append((a, y))
        S.add((a, y))
        nb_x.add(b)
        nb_y.add(a)
    if len(nb_x) < d:
        return None
    return old + 2


def _anneal(n, E, S, D, end, rng):
    """Double-edge swaps (degree-preserving, A-B preserving) minimising bad pairs.

    Modifies E and S in place. Returns True iff cost reached zero before `end`.
    """
    cost = _bad_pairs(n, E, D)
    if cost == 0:
        return True
    t0 = time.monotonic()
    span = max(1e-3, end - t0)
    m = len(E)
    T0, T1 = 3.0, 0.1
    while True:
        now = time.monotonic()
        if now >= end:
            return False
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e:
            continue
        f1 = (a, e)
        f2 = (c, b)
        if f1 in S or f2 in S:
            continue
        E[i] = f1
        E[j] = f2
        S.discard((a, b))
        S.discard((c, e))
        S.add(f1)
        S.add(f2)
        new = _bad_pairs(n, E, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost = new
            if cost == 0:
                return True
        else:
            E[i] = (a, b)
            E[j] = (c, e)
            S.discard(f1)
            S.discard(f2)
            S.add((a, b))
            S.add((c, e))


def _search(n, edges, d, D, deadline, rng):
    """Repeatedly grow by one A-B vertex pair and repair with annealing. Returns best valid (n, edges)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    color = _sides(n, adj)
    cur_E = [(u, v) if color[u] == 0 else (v, u) for u, v in edges]
    cur_n = n
    best = (n, list(edges))
    total = max(1.0, deadline - time.monotonic())
    while True:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        att_end = now + min(remaining, max(2.0, 0.2 * total))
        E = list(cur_E)
        S = set(E)
        nn = _insert_pair(cur_n, E, S, d, rng)
        if nn is None:
            continue
        if _anneal(nn, E, S, D, att_end, rng):
            cand = (nn, list(E))
            if lib.is_valid(nn, cand[1], d, D):
                best = cand
                cur_n, cur_E = nn, list(E)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(g):
        nonlocal best
        if g is None:
            return
        n, e = g
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Moore-optimal for D = 3 when d-1 is a prime power; valid for any D >= 3.
    if lib.is_prime_power(d - 1):
        consider(lib.projective_plane_incidence(d - 1))
        return best

    # Record base for D = 3 when d-2 is a prime power.
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    # Plain projective plane with q <= d-2 (diameter 3, valid for D >= 3).
    try:
        consider(_pg_candidate(d))
    except Exception:
        pass

    if D == 3 and best[0] > 2 * d:
        try:
            best = _search(best[0], best[1], d, D, deadline, rng)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
