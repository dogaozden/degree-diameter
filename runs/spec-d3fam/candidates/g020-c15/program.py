import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (diameter 3 when available).
# ----------------------------------------------------------------------------

def _ara(d):
    """Araujo-Pardo & Lopez graph for d = q + 2, q a prime power (diameter 3)."""
    q = d - 2
    if 3 <= q <= 30 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _pg(d):
    """Point-line incidence graph of PG(2, q) for the largest prime power q <= d - 1 (diameter 3)."""
    for q in range(min(d - 1, 30), 1, -1):
        if lib.is_prime_power(q):
            try:
                return lib.projective_plane_incidence(q)
            except Exception:
                return None
    return None


# ----------------------------------------------------------------------------
# Bipartite helpers.
# ----------------------------------------------------------------------------

def _colour(n, edges):
    """Two-colouring by BFS; entries are -1 for vertices in no component reached (should not happen)."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
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


def _oriented_pairs(col, edges):
    """Edges as (side0, side1) pairs."""
    return [(u, v) if col[u] == 0 else (v, u) for u, v in edges]


# ----------------------------------------------------------------------------
# Growth by annealing: add one A and one B vertex to a valid graph, then
# anneal (degree-preserving 2-swaps and endpoint moves) until diameter <= D.
# ----------------------------------------------------------------------------

def _attempt(n, col, pairs, d, D, deadline, rng):
    """Try to grow a valid bipartite graph by two vertices. Returns (n2, col2, pairs2) or None."""
    n2 = n + 2
    col2 = list(col) + [0, 1]
    pairs = list(pairs)

    # Remove d random edges to free stubs for the two new vertices.
    for _ in range(min(d, len(pairs))):
        i = rng.randrange(len(pairs))
        pairs[i], pairs[-1] = pairs[-1], pairs[i]
        pairs.pop()

    eset = set(pairs)
    deg = [0] * n2
    for a, b in pairs:
        deg[a] += 1
        deg[b] += 1

    side0 = [v for v in range(n2) if col2[v] == 0]
    side1 = [v for v in range(n2) if col2[v] == 1]

    # Greedy fill of deficient opposite-side pairs.
    dA = [a for a in side0 if deg[a] < d]
    dB = [b for b in side1 if deg[b] < d]
    cand = [(a, b) for a in dA for b in dB if (a, b) not in eset]
    rng.shuffle(cand)
    for a, b in cand:
        if deg[a] < d and deg[b] < d and (a, b) not in eset:
            pairs.append((a, b))
            eset.add((a, b))
            deg[a] += 1
            deg[b] += 1

    if not pairs:
        return None

    cur = lib.bad_pairs(n2, pairs, D)
    T0 = 1.5
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = T0 * (0.01 ** frac)
        m = len(pairs)

        if m >= 2 and rng.random() < 0.6:
            # Degree-preserving double-edge swap.
            i = rng.randrange(m)
            j = rng.randrange(m)
            a, b = pairs[i]
            c, e = pairs[j]
            if a == c or b == e or (a, e) in eset or (c, b) in eset:
                continue
            pairs[i] = (a, e)
            pairs[j] = (c, b)
            eset.discard((a, b))
            eset.discard((c, e))
            eset.add((a, e))
            eset.add((c, b))
            new = lib.bad_pairs(n2, pairs, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                pairs[i] = (a, b)
                pairs[j] = (c, e)
                eset.discard((a, e))
                eset.discard((c, b))
                eset.add((a, b))
                eset.add((c, e))
        else:
            # Move one endpoint of an edge to another side-1 vertex with spare degree.
            i = rng.randrange(m)
            a, b = pairs[i]
            e = rng.choice(side1)
            if e == b or deg[e] >= d or (a, e) in eset:
                continue
            pairs[i] = (a, e)
            eset.discard((a, b))
            eset.add((a, e))
            deg[b] -= 1
            deg[e] += 1
            new = lib.bad_pairs(n2, pairs, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                pairs[i] = (a, b)
                eset.discard((a, e))
                eset.add((a, b))
                deg[e] -= 1
                deg[b] += 1

    return n2, col2, pairs


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        starts = []
        for cand in (_ara(d), _pg(d)):
            if cand is not None:
                consider(cand[0], cand[1])
                starts.append(cand)

        # Growth search for diameter 3, starting from the largest valid base.
        if D == 3 and d >= 3 and starts:
            n0, e0 = max(starts, key=lambda c: c[0])
            if lib.is_valid(n0, e0, d, D):
                col = _colour(n0, e0)
                if all(c in (0, 1) for c in col):
                    cur_n, cur_col, cur_pairs = n0, col, _oriented_pairs(col, e0)
                    while time.monotonic() < deadline:
                        remaining = deadline - time.monotonic()
                        attempt_deadline = time.monotonic() + max(2.0, 0.4 * remaining)
                        attempt_deadline = min(attempt_deadline, deadline)
                        res = _attempt(cur_n, cur_col, cur_pairs, d, D, attempt_deadline, rng)
                        if res is None:
                            continue
                        cur_n, cur_col, cur_pairs = res
                        new_edges = list(cur_pairs)
                        consider(cur_n, new_edges)

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, best_e
