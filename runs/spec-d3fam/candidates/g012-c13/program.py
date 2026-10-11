import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Helpers
# ----------------------------------------------------------------------------

def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets."""
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


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


# ----------------------------------------------------------------------------
# Degree-preserving growth by two vertices (point P and line L).
# ----------------------------------------------------------------------------

def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices using a d-matching rewire, then anneal with 2-switches.

    The 2-switches keep all degrees and the bipartition, and minimise the number
    of pairs at distance > D. The temperature decays with elapsed time.
    Returns (n+2, edges) with diameter <= D, or None if the search fails in time.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1                      # P has colour 1, L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (colour0, colour1)
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = max(0.02, 0.02 ** frac)          # decays from 1.0 to 0.02 over the budget
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        # 2-switch: (a,b),(c,e) -> (a,e),(c,b); keeps colour0-colour1 orientation
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return N, list(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Candidate bases: K_{d,d} (diameter 2, always valid for D >= 2),
    # the Araujo-Pardo & Lopez record graph (D = 3, d = q + 2), and PG(2, q)
    # for the largest prime power q <= d - 1 (D = 3).
    cands = [lib.haar_graph(d, range(d))]
    if D >= 3:
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                cands.append(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        q = next((x for x in range(d - 1, 1, -1) if lib.is_prime_power(x)), None)
        if q is not None:
            cands.append(lib.projective_plane_incidence(q))

    best = None
    for n0, e0 in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n0, e0, d, D):
            best = (n0, e0)
            break
    if best is None:
        return lib.haar_graph(d, range(d))

    # Grow by two vertices at a time while the Moore bound allows and time remains.
    # Each attempt gets a share of the remaining time; failures retry with new randomness.
    n, e = best
    mb = _moore(d, D)
    while n + 2 <= mb:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 0.5:
            break
        attempt_deadline = now + 0.6 * remaining
        res = _augment(n, e, d, D, rng, attempt_deadline)
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            n, e = res
        # On failure, loop again with fresh randomness until time runs out.

    if not lib.is_valid(n, e, d, D):
        return lib.haar_graph(d, range(d))
    return n, e
