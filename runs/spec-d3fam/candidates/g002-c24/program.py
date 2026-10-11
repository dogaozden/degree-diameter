import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (all valid for D >= 3).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_base(d):
    """Araujo-Pardo and Lopez record graph (degree q+2) when q = d-2 is a prime power >= 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except (ValueError, AssertionError):
        return None


# ----------------------------------------------------------------------------
# Graph helpers on adjacency sets.
# ----------------------------------------------------------------------------

def _two_color(n, adj):
    """Proper 2-colouring of a bipartite graph given as adjacency sets."""
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
    """Number of unordered pairs at distance > D (unreachable pairs included)."""
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


def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


# ----------------------------------------------------------------------------
# Repair-based vertex growth by simulated annealing.
#
# Fix a target order n2 = n + extra, start from a valid graph plus extra
# vertices, and anneal over degree-respecting moves (double-edge swaps,
# edge insertions, edge deletions) minimising the number of pairs at
# distance > D. Reaching cost 0 yields a larger valid graph.
# ----------------------------------------------------------------------------

def _sa_extend(n, adj, color, d, D, extra, budget, rng):
    """Try to find a valid graph on n + extra vertices within `budget` seconds."""
    t_end = time.monotonic() + budget
    adj = [set(s) for s in adj]
    color = list(color)
    for t in range(extra):
        adj.append(set())
        color.append(t % 2)
    n2 = n + extra

    # Greedy saturation of the new vertices against spare-degree opposite vertices.
    for v in range(n, n2):
        opp = [u for u in range(n2)
               if color[u] != color[v] and u not in adj[v] and len(adj[u]) < d]
        rng.shuffle(opp)
        for u in opp:
            if len(adj[v]) >= d:
                break
            if len(adj[u]) < d:
                adj[v].add(u)
                adj[u].add(v)

    cur = _bad_pairs(n2, adj, D)
    if cur == 0:
        return n2, adj, color

    T0, T1 = 2.0, 0.15
    start = time.monotonic()
    span = max(1e-6, budget)

    while True:
        now = time.monotonic()
        if now >= t_end:
            break
        frac = (now - start) / span
        T = T0 * (T1 / T0) ** frac
        r = rng.random()

        if r < 0.1:
            # Edge deletion (escape move).
            a = rng.randrange(n2)
            if not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            adj[a].discard(b)
            adj[b].discard(a)
            new = _bad_pairs(n2, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a].add(b)
                adj[b].add(a)

        elif r < 0.3:
            # Edge insertion between two deficient opposite-side vertices.
            a = rng.randrange(n2)
            b = rng.randrange(n2)
            if color[a] != 0 or color[b] != 1:
                continue
            if len(adj[a]) >= d or len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            cur = _bad_pairs(n2, adj, D)

        else:
            # Degree-preserving double-edge swap:
            # (a,b),(c,e) -> (a,c),(e,b), with a,e on side 0 and b,c on side 1.
            a = rng.randrange(n2)
            if color[a] != 0 or not adj[a]:
                continue
            b = rng.choice(tuple(adj[a]))
            c = rng.randrange(n2)
            if color[c] != 1 or c == b or c in adj[a] or not adj[c]:
                continue
            e = rng.choice(tuple(adj[c]))
            if e == a or b in adj[e]:
                continue
            adj[a].discard(b)
            adj[b].discard(a)
            adj[c].discard(e)
            adj[e].discard(c)
            adj[a].add(c)
            adj[c].add(a)
            adj[e].add(b)
            adj[b].add(e)
            new = _bad_pairs(n2, adj, D)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                adj[a].discard(c)
                adj[c].discard(a)
                adj[e].discard(b)
                adj[b].discard(e)
                adj[a].add(b)
                adj[b].add(a)
                adj[c].add(e)
                adj[e].add(c)

        if cur == 0:
            return n2, adj, color

    return None


# ----------------------------------------------------------------------------
# Top level.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    # K_{d,d}: bipartite, degree d, diameter 2. Safe for every D >= 2.
    fallback = lib.haar_graph(d, range(d))
    if D == 2:
        return fallback

    # Choose the largest valid structured base for D >= 3.
    best = fallback
    for cand in (_araujo_base(d), _pg_base(d)):
        if cand is None:
            continue
        if cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    n = best[0]
    adj = [set() for _ in range(n)]
    for u, v in best[1]:
        adj[u].add(v)
        adj[v].add(u)
    color = _two_color(n, adj)

    # Bold step: repair-based growth by annealing, starting from the base.
    extra = 2
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        budget = remaining * 0.5
        res = _sa_extend(n, adj, color, d, D, extra, budget, rng)
        if res is None:
            if extra == 1:
                break
            extra = 1
            continue
        n2, adj2, color2 = res
        E2 = _edges_of(n2, adj2)
        if not lib.is_valid(n2, E2, d, D):
            break
        n, adj, color = n2, adj2, color2
        best = (n2, E2)
        extra = 2

    if not lib.is_valid(best[0], best[1], d, D):
        return fallback
    return best
