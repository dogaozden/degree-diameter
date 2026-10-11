import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (known records / projective planes).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


def _bipartite_sides(n, edges):
    """Two-colouring of the graph, or None if it is not bipartite."""
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
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


# ----------------------------------------------------------------------------
# New family: edge-switch annealing with degree-preserving pair growth.
#
# State: a bipartite graph with max degree <= d, stored as E = [(side0, side1), ...]
# and adjacency sets. Moves:
#   * grow: add a new pair (v on side 0, w on side 1). Pick d edges (a_i, b_i) with
#     distinct endpoints; replace each by (a_i, w) and add (v, b_i). Every old degree
#     is preserved and v, w get degree d. Diameter may break.
#   * switch: (a,b),(c,e) -> (a,e),(c,b). Degrees are preserved, bipartiteness too.
# Simulated annealing on the number of vertex pairs at distance > D drives the
# cost to zero, after which growth continues.
# ----------------------------------------------------------------------------

def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance > D (0 means diameter <= D)."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return sum(n - b.bit_count() for b in ball) // 2


def _grow_search(n0, edges0, d, D, color, deadline, rng, step_iters):
    """Grow from a valid graph by pair-additions, repairing diameter by edge switches.

    Returns the largest valid (n, edges) found (or None if the start was never extended).
    """
    n = n0
    E = [((u, v) if color[u] == 0 else (v, u)) for u, v in edges0]
    adj = [set() for _ in range(n)]
    for a, b in E:
        adj[a].add(b)
        adj[b].add(a)

    def replace(idx, new):
        old = E[idx]
        adj[old[0]].discard(old[1])
        adj[old[1]].discard(old[0])
        adj[new[0]].add(new[1])
        adj[new[1]].add(new[0])
        E[idx] = new

    best = None
    cur = _cost(n, adj, D)
    if cur == 0:
        best = (n, list(E))

    while time.monotonic() < deadline and cur == 0:
        # ---- grow by one pair (keeps all degrees <= d) ----
        m = len(E)
        if m < d:
            break
        chosen, used_a, used_b, chosen_set = [], set(), set(), set()
        tries = 0
        while len(chosen) < d and tries < 50 * d:
            tries += 1
            i = rng.randrange(m)
            if i in chosen_set:
                continue
            a, b = E[i]
            if a in used_a or b in used_b:
                continue
            chosen.append(i)
            chosen_set.add(i)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d:
            break
        v, w = n, n + 1
        n += 2
        adj.append(set())
        adj.append(set())
        for i in chosen:
            a, b = E[i]
            replace(i, (a, w))
            adj[v].add(b)
            adj[b].add(v)
            E.append((v, b))
        cur = _cost(n, adj, D)

        # ---- anneal with edge switches until diameter is repaired ----
        T = 1.5
        decay = (0.05 / 1.5) ** (1.0 / max(1, step_iters))
        for _ in range(step_iters):
            if cur == 0 or time.monotonic() > deadline:
                break
            T *= decay
            m = len(E)
            i = rng.randrange(m)
            j = rng.randrange(m)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            old1, old2 = E[i], E[j]
            replace(i, (a, e))
            replace(j, (c, b))
            c2 = _cost(n, adj, D)
            delta = c2 - cur
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cur = c2
            else:
                replace(i, old1)
                replace(j, old2)

        if cur == 0:
            best = (n, list(E))
        else:
            break
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} (diameter 2).
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d == 2:
        # Cycle C_{2D} is optimal for d = 2.
        n = 2 * D
        cand = (n, [(i, (i + 1) % n) for i in range(n)])
        if lib.is_valid(cand[0], cand[1], d, D):
            return cand
        return best

    if D == 2:
        return best

    # Valid starting bases for D >= 3.
    starts = []
    for cand in (_araujo(d), _best_pg(d)):
        if cand is None:
            continue
        consider(cand)
        starts.append(cand)

    # Edge-switch annealing growth from the largest valid base.
    starts = [c for c in starts if lib.is_valid(c[0], c[1], d, D)]
    starts.sort(key=lambda c: -c[0])
    for base_n, base_e in starts[:1]:
        color = _bipartite_sides(base_n, base_e)
        if color is None:
            continue
        res = _grow_search(base_n, base_e, d, D, color, deadline, rng, step_iters=3000)
        consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
