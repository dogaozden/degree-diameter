"""Diameter-D bipartite graph builder.

New routine in this version: PAIR INSERTION WITH DEGREE-PRESERVING 2-SWITCH ANNEALING.

Given a valid bipartite graph G with max degree d, add two new vertices x (side 0) and y (side 1):
repeatedly pick an existing edge (u, v) with u on side 0 and v on side 1, delete it, and add
(u, y) and (x, v). Every old vertex keeps its degree, and x and y each gain one neighbour per step,
so after d steps both have degree d. The result is bipartite and has max degree d, but its diameter
is usually too large. Degree-preserving 2-switches (replace (a1,b1),(a2,b2) by (a1,b2),(a2,b1))
then anneal the number of vertex pairs at distance > D toward zero. Success gives a valid graph with
two more vertices, and the step is repeated from the new graph while time remains.
"""
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Graph state helpers.  A state is (n, col, E, adj):
#   col[v] in {0, 1} is the side of v,
#   E is a list of [a, b] with a on side 0 and b on side 1,
#   adj[v] is a set of neighbours.
# ----------------------------------------------------------------------------

def _bipartition(n, adj_lists):
    """Two-colouring of a bipartite graph given by adjacency lists."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj_lists[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _orient(n, edges):
    """Return (col, E) with each edge oriented from side 0 to side 1."""
    adj_lists = [[] for _ in range(n)]
    for u, v in edges:
        adj_lists[u].append(v)
        adj_lists[v].append(u)
    col = _bipartition(n, adj_lists)
    E = [[u, v] if col[u] == 0 else [v, u] for u, v in edges]
    return col, E


def _adj_sets(n, E):
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)
    return adj


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _add_pair(n, col, E, adj, d, rng):
    """Insert new vertices x (side 0) and y (side 1) by stealing edges from G.

    Each step removes an edge (u, v), then adds (u, y) and (x, v). Old degrees are unchanged,
    and x and y each gain one neighbour per step, so both reach degree d.
    Returns (n, col, E, adj, ok).
    """
    x, y = n, n + 1
    n += 2
    col = col + [0, 1]
    adj.append(set())
    adj.append(set())
    tries = 0
    while len(adj[x]) < d and E and tries < 200000:
        tries += 1
        i = rng.randrange(len(E))
        u, v = E[i]
        if v in adj[x] or u in adj[y]:
            continue
        adj[u].discard(v)
        adj[v].discard(u)
        E[i] = [u, y]
        adj[u].add(y)
        adj[y].add(u)
        E.append([x, v])
        adj[x].add(v)
        adj[v].add(x)
    return n, col, E, adj, len(adj[x]) == d


def _anneal(n, E, adj, D, deadline, rng):
    """Degree-preserving 2-switch annealing until every pair is within distance D.

    A move with new cost c2 is accepted iff c2 <= cost - T*ln(u), u ~ Uniform(0, 1].
    Temperature decays geometrically from 1.0 to 0.05 over the deadline window.
    Returns True when the cost reaches zero (E and adj then hold a valid graph).
    """
    cur = _cost(n, adj, D)
    start = time.monotonic()
    span = max(1e-6, deadline - start)
    T0, T1 = 1.0, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - start) / span)
        m = len(E)
        i = rng.randrange(m)
        j = rng.randrange(m)
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2 or b2 in adj[a1] or b1 in adj[a2]:
            continue
        adj[a1].discard(b1)
        adj[b1].discard(a1)
        adj[a2].discard(b2)
        adj[b2].discard(a2)
        adj[a1].add(b2)
        adj[b2].add(a1)
        adj[a2].add(b1)
        adj[b1].add(a2)
        c2 = _cost(n, adj, D)
        if c2 <= cur - T * math.log(1.0 - rng.random()):
            cur = c2
            E[i] = [a1, b2]
            E[j] = [a2, b1]
        else:
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)
    return cur == 0


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
    if D == 2:
        return lib.haar_graph(d, range(d))  # K_{d,d}: diameter 2

    # Candidate bases, all valid for diameter D >= 3.
    cands = [lib.haar_graph(d, range(d))]  # K_{d,d} fallback
    pg = _best_pg(d)
    if pg is not None:
        cands.append(pg)
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            cands.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    valid = [c for c in cands if lib.is_valid(c[0], c[1], d, D)]
    best = max(valid, key=lambda c: c[0])
    best_n, best_e = best

    # Growth by pair insertion, starting from the largest valid base.
    moore = lib._moore_bound(d, D)
    if best_n < moore:
        col, E = _orient(best_n, best_e)
        n = best_n
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.5:
                break
            attempt_deadline = now + 0.5 * remaining
            n2, col2, E2, adj2, ok = _add_pair(
                n, list(col), [list(e) for e in E], _adj_sets(n, E), d, rng)
            if not ok:
                break
            if _anneal(n2, E2, adj2, D, attempt_deadline, rng):
                n, col, E = n2, col2, E2
                if n >= moore:
                    break
        grown_e = [(a, b) for a, b in E]
        if n > best_n and lib.is_valid(n, grown_e, d, D):
            best_n, best_e = n, grown_e

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
