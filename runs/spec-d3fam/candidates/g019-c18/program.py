import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _ara(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power >= 3 (diameter 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Repair search: grow a d-regular bipartite graph of diameter 3 by one vertex per side.
#
# For a d-regular bipartite graph, diameter <= 3 is equivalent (up to opposite-side
# pairs, which are verified at the end) to: every two vertices on the same side share
# a neighbour. The search keeps the graph d-regular and minimises the number of
# uncovered same-side pairs, using degree-preserving edge swaps.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Bipartition of a graph given by adjacency lists, or None if not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _unc(S, M, h):
    """Uncovered pairs that involve at least one vertex of S (pairs inside S counted once)."""
    tot = 0
    for x in S:
        mx = M[x]
        for y in range(h):
            if y == x:
                continue
            if y in S and y < x:
                continue
            if not (mx & M[y]):
                tot += 1
    return tot


def _full(M, h):
    """Total number of uncovered pairs on one side."""
    tot = 0
    for x in range(h):
        mx = M[x]
        for y in range(x + 1, h):
            if not (mx & M[y]):
                tot += 1
    return tot


def _repair(d, D, n0, edges0, deadline, rng):
    """Try to extend a d-regular diameter-3 bipartite graph by one vertex per side.

    Returns (n0 + 2, edges) if a valid graph is found before the deadline, else None.
    """
    adj = lib.adjacency(n0, edges0)
    if any(len(a) != d for a in adj):
        return None
    color = _two_color(n0, adj)
    if color is None:
        return None

    oriented = [(u, v) if color[u] == 0 else (v, u) for u, v in edges0]

    # Remove a random matching of d edges and reattach it through the two new vertices.
    chosen, order = None, None
    for _ in range(50):
        order = oriented[:]
        rng.shuffle(order)
        used_a, used_b, pick = set(), set(), []
        for idx, (a, b) in enumerate(order):
            if a not in used_a and b not in used_b:
                pick.append(idx)
                used_a.add(a)
                used_b.add(b)
                if len(pick) == d:
                    break
        if len(pick) == d:
            chosen = pick
            break
    if chosen is None:
        return None

    x, y = n0, n0 + 1  # new A-side and B-side vertices
    chosen_set = set(chosen)
    Ag = [v for v in range(n0) if color[v] == 0] + [x]
    Bg = [v for v in range(n0) if color[v] == 1] + [y]
    if len(Ag) != len(Bg):
        return None
    ai = {v: i for i, v in enumerate(Ag)}
    bi = {v: i for i, v in enumerate(Bg)}
    h = len(Ag)

    E = []
    for idx, (a, b) in enumerate(order):
        if idx not in chosen_set:
            E.append([ai[a], bi[b]])
    for idx in chosen:
        a, b = order[idx]
        E.append([ai[x], bi[b]])
        E.append([ai[a], bi[y]])
    if len(E) != h * d:
        return None

    NA = [0] * h  # NA[a] = bitmask over B-indices of neighbours of a
    NB = [0] * h  # NB[b] = bitmask over A-indices of neighbours of b
    for a, b in E:
        NA[a] |= 1 << b
        NB[b] |= 1 << a

    cur = _full(NA, h) + _full(NB, h)
    t0 = time.monotonic()
    span = max(1e-6, deadline - t0)
    m = len(E)
    if m < 2:
        return None

    while True:
        now = time.monotonic()
        if now >= deadline:
            break

        if cur == 0:
            Ee = [(Ag[a], Bg[b]) for a, b in E]
            if lib.is_valid(n0 + 2, Ee, d, D):
                return n0 + 2, Ee

        frac = (now - t0) / span
        T = 0.6 * (0.03 / 0.6) ** frac

        i = rng.randrange(m)
        j = rng.randrange(m)
        if i == j:
            continue
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            continue
        if (NA[a1] >> b2) & 1 or (NA[a2] >> b1) & 1:
            continue

        c0 = _unc((a1, a2), NA, h) + _unc((b1, b2), NB, h)
        flip_a = (1 << b1) | (1 << b2)
        flip_b = (1 << a1) | (1 << a2)
        NA[a1] ^= flip_a
        NA[a2] ^= flip_a
        NB[b1] ^= flip_b
        NB[b2] ^= flip_b
        c1 = _unc((a1, a2), NA, h) + _unc((b1, b2), NB, h)
        delta = c1 - c0

        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = [a1, b2]
            E[j] = [a2, b1]
            cur += delta
        else:
            NA[a1] ^= flip_a
            NA[a2] ^= flip_a
            NB[b1] ^= flip_b
            NB[b2] ^= flip_b

    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

        ara = _ara(d)
        if ara is not None:
            consider(ara[0], ara[1])

            # Repair search: repeatedly grow the current d-regular graph by two vertices.
            cur_n, cur_e = ara[0], ara[1]
            while True:
                now = time.monotonic()
                remaining = deadline - now
                if remaining < 0.5:
                    break
                step_deadline = now + 0.6 * remaining
                res = _repair(d, D, cur_n, cur_e, step_deadline, rng)
                if res is None:
                    break
                cur_n, cur_e = res
                consider(cur_n, cur_e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
