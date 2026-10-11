import math
import random
import time

import lib

ITERS = 600               # annealing steps per (group, voltage) try
GROUPS_PER_VARIANT = 6    # groups tried per (lift size, base-shape) variant


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Groups.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when r = 1 and k = 1)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# New idea: two-sided voltage lifts with a 2a-vertex base.
#
# Base: a A-vertices and a B-vertices, with a bipartite multigraph M of
# constant degree d (M[i][j] parallel darts between A_i and B_j).  Each dart
# carries a group voltage g, joining (A_i, x) to (B_j, x*g) for all x in G.
# Left multiplication by y is an automorphism, so the distances from all
# (w, x) are determined by the 2a sources (w, identity).  That makes the
# diameter check cost 2a BFS runs on a graph of 2a*|G| vertices, which is
# cheap enough to anneal over voltages for orders beyond the bi-Cayley case.
# a = 1 is the bi-Cayley family; a = 2 gives the new two-orbit lifts.
# ----------------------------------------------------------------------------

def _nbrs(a, darts, vals, invs):
    """Base-level adjacency: nb[w] lists (w2, h) so that (w, x) ~ (w2, x*h)."""
    nb = [[] for _ in range(2 * a)]
    for (i, j), g in zip(darts, vals):
        nb[i].append((a + j, g))
        nb[a + j].append((i, invs[g]))
    return nb


def _cost(N, a, nb, T, D):
    """Ordered (source, vertex) pairs not within distance D, sources = (w, identity) for each base vertex w."""
    n = 2 * a * N
    total = 0
    for s in range(2 * a):
        seen = bytearray(n)
        src = s * N
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for idx in frontier:
                w, x = divmod(idx, N)
                row = T[x]
                for w2, h in nb[w]:
                    v = w2 * N + row[h]
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += n - count
    return total


def _anneal(N, a, darts, T, invs, D, rng, deadline):
    """Anneal voltages so that every base source reaches everything within D; None on failure."""
    vals = []
    used = {}
    for pair in darts:
        s = used.setdefault(pair, set())
        c = rng.randrange(N)
        while c in s:
            c = rng.randrange(N)
        s.add(c)
        vals.append(c)
    same = [[q for q in range(len(darts)) if q != k and darts[q] == darts[k]]
            for k in range(len(darts))]
    cur = _cost(N, a, _nbrs(a, darts, vals, invs), T, D)
    for it in range(ITERS):
        if cur == 0:
            return vals
        if time.monotonic() > deadline:
            break
        k = rng.randrange(len(darts))
        c = rng.randrange(N)
        if any(vals[q] == c for q in same[k]):
            continue
        new = vals[:]
        new[k] = c
        v = _cost(N, a, _nbrs(a, darts, new, invs), T, D)
        temp = max(0.3, 3.0 * (1.0 - it / ITERS))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            vals, cur = new, v
    return vals if cur == 0 else None


def _variant(a, N, d, D, rng, deadline):
    """Search a lift of order 2*a*N; return (n, edges) if a valid graph is found."""
    if a == 1:
        M = [[d]]
    else:
        x = rng.randrange(1, d)            # 1 <= x <= d-1 keeps the base connected
        M = [[x, d - x], [d - x, x]]
    darts = [(i, j) for i in range(a) for j in range(a) for _ in range(M[i][j])]
    if not darts:
        return None
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_VARIANT]:
        if time.monotonic() >= deadline:
            break
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, h) for h in range(N)] for x in range(N)]
        invs = [inv(h) for h in range(N)]
        vals = _anneal(N, a, darts, T, invs, D, rng, deadline)
        if vals is None:
            continue
        n = 2 * a * N
        edges = []
        for (i, j), g in zip(darts, vals):
            for x in range(N):
                edges.append((i * N + x, (a + j) * N + T[x][g]))
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def _attempt_total(T, d, D, rng, deadline):
    """Try to build a valid graph with exactly T vertices (T even)."""
    variants = [(1, T // 2)]
    if T % 4 == 0 and d >= 2:
        variants.append((2, T // 4))
    for idx, (a, N) in enumerate(variants):
        now = time.monotonic()
        if now >= deadline:
            return None
        sub = now + (deadline - now) / (len(variants) - idx)
        res = _variant(a, N, d, D, rng, min(deadline, sub))
        if res is not None:
            return res
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.85 * time_limit - 2.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Record-matching calibration case.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
        return best

    consider(*lib.haar_graph(d, range(d)))
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    hi = lib._moore_bound(d, D)
    T = max(best[0] + 2, int(0.49 * hi))
    if T % 2:
        T += 1

    budget = 1.0
    tries = 0
    while time.monotonic() < deadline and T <= hi:
        att_deadline = min(deadline, time.monotonic() + budget)
        res = _attempt_total(T, d, D, rng, att_deadline)
        if res is not None:
            consider(*res)
            T = max(T, res[0]) + 2
            budget = 1.0
            tries = 0
        else:
            tries += 1
            budget = min(budget * 1.5, 25.0)
            if tries >= 4:
                T += 2
                budget = 1.0
                tries = 0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
