import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Graph helpers.
# ----------------------------------------------------------------------------

def _adj_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph given by neighbour sets (-1 if uncoloured)."""
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
    return color


def _bad_pairs(n, adj, D):
    """Number of unordered vertex pairs at distance > D (unreachable pairs included)."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach) // 2


def _saturate(n, adj, color, d, rng):
    """Add edges between deficient opposite-side vertices. Adding edges never breaks diameter."""
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


# ----------------------------------------------------------------------------
# NEW: pair insertion by edge switching, with diameter annealing.
#
# The graph is kept bipartite (side 0 = "A", side 1 = "B"); every edge is stored
# as (a, b) with a in A. A new vertex pair (x in A, y in B) is inserted by
# "edge splitting": pick an existing edge (a, b), delete it, and add (x, b) and
# (a, y). Degrees of a and b are unchanged, and x and y each gain one edge per
# split, so the degree bound is kept and the order grows by 2 with no degree
# overflow. The remaining objective, the number of pairs at distance > D, is
# then reduced by simulated annealing over degree-preserving 2-switches
# (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). The search only ever keeps states with
# zero bad pairs, so every stored graph is valid.
# ----------------------------------------------------------------------------

def _search(n, adj, color, d, D, deadline, rng):
    """Grow a valid graph by pair insertion plus annealed switches. Returns (n, edges) or None."""
    E = [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]
    cur = _bad_pairs(n, adj, D)
    best = (n, list(E)) if cur == 0 else None
    good = None
    if cur == 0:
        good = (n, list(E), [set(s) for s in adj], list(color))
    T = 0.5
    STALL = 2500
    stall = 0
    minseen = cur

    while time.monotonic() < deadline:
        if cur == 0:
            # Record this zero-cost state, then insert a new pair of vertices.
            if best is None or n > best[0]:
                best = (n, list(E))
            good = (n, list(E), [set(s) for s in adj], list(color))
            old_n = n
            x, y = n, n + 1
            n += 2
            color.append(0)
            color.append(1)
            adj.append(set())
            adj.append(set())
            tries = 0
            while len(adj[x]) < d and len(adj[y]) < d and tries < 5000 and E:
                tries += 1
                i = rng.randrange(len(E))
                a, b = E[i]
                if a >= old_n or b >= old_n:
                    continue
                if b in adj[x] or a in adj[y]:
                    continue
                adj[a].discard(b)
                adj[b].discard(a)
                adj[x].add(b)
                adj[b].add(x)
                adj[a].add(y)
                adj[y].add(a)
                E[i] = (x, b)
                E.append((a, y))
            cur = _bad_pairs(n, adj, D)
            stall = 0
            minseen = cur
            continue

        if stall > STALL and good is not None:
            # Stuck: roll back to the last zero-cost graph and grow again.
            n = good[0]
            E = list(good[1])
            adj = [set(s) for s in good[2]]
            color = list(good[3])
            cur = 0
            continue

        stall += 1
        if len(E) < 2:
            break
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        if i == j:
            continue
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
        new = _bad_pairs(n, adj, D)
        delta = new - cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = (a1, b2)
            E[j] = (a2, b1)
            cur = new
            if cur < minseen:
                minseen = cur
                stall = 0
            if cur == 0:
                continue
        else:
            adj[a1].discard(b2)
            adj[b2].discard(a1)
            adj[a2].discard(b1)
            adj[b1].discard(a2)
            adj[a1].add(b1)
            adj[b1].add(a1)
            adj[a2].add(b2)
            adj[b2].add(a2)

    if cur == 0 and (best is None or n > best[0]):
        best = (n, list(E))
    return best


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    best = (best_n, best_e)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best

    if D == 3:
        # Moore-optimal: PG(2, d-1) incidence graph is d-regular with diameter 3.
        if lib.is_prime_power(d - 1):
            consider(*lib.projective_plane_incidence(d - 1))
            return best
        # Araujo-Pardo & Lopez record family for d-2 a prime power.
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except (ValueError, StopIteration, KeyError):
                pass

    if D >= 3:
        # Largest projective plane incidence graph that fits degree d.
        for q in range(d - 1, 1, -1):
            if lib.is_prime_power(q):
                consider(*lib.projective_plane_incidence(q))
                break

    # Main search: pair insertion plus annealed switches on the best base.
    n, edges = best
    adj = _adj_sets(n, edges)
    color = _two_color(n, adj)
    if any(c < 0 for c in color):
        return best
    _saturate(n, adj, color, d, rng)

    res = _search(n, adj, color, d, D, deadline, rng)
    if res is not None:
        consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
