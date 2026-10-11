import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bounded-degree bipartite growth with local repair.
#
# Start from a valid base graph (Araujo-Pardo-Lopez or projective plane when
# available, otherwise K_{d,d}). Repeatedly add one vertex, attached greedily to
# a set of opposite-side vertices that covers as much of the radius-(D-1) ball
# structure as possible. Then repair the diameter by simulated-annealing edge
# moves (degree-preserving cross-side swaps) and greedy saturation. A grown graph
# is kept only if it becomes valid again; otherwise the last valid graph stands.
# ----------------------------------------------------------------------------


def _balls(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _cost(n, adj, D):
    """Number of unordered vertex pairs at distance greater than D."""
    ball = _balls(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _bipartition(n, adj):
    """Two-colouring of a bipartite graph given by adjacency sets."""
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


def _candidates(d):
    """Structured base graphs usable as starting points for diameter 3."""
    out = []
    if d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            out.append(lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            out.append(lib.projective_plane_incidence(q))
            break
    return out


def _add_vertex(n, adj, color, d, D, rng):
    """Append one vertex on a random side, joined to up to d opposite vertices chosen greedily.

    Neighbours that already have full degree lose one random edge first, so that
    degrees stay at most d. Returns the new vertex count.
    """
    c = rng.randrange(2)
    ball = _balls(n, adj, D - 1)
    covered = 0
    pool = [s for s in range(n) if color[s] != c]
    chosen = []
    while pool and len(chosen) < d:
        best_g, best_i = -1, -1
        for i, s in enumerate(pool):
            g = (ball[s] & ~covered).bit_count()
            if g > best_g or (g == best_g and rng.random() < 0.3):
                best_g, best_i = g, i
        if best_g <= 0:
            break
        s = pool.pop(best_i)
        chosen.append(s)
        covered |= ball[s]

    v = n
    color.append(c)
    adj.append(set())
    for s in chosen:
        if len(adj[s]) >= d:
            y = rng.choice(list(adj[s]))
            adj[s].discard(y)
            adj[y].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return n + 1


def _repair(n, adj, color, d, D, rng, deadline, budget):
    """Annealed repair: greedy saturation plus degree-preserving cross-side edge swaps.

    Returns True if the diameter condition holds at the end.
    """
    cur = _cost(n, adj, D)
    T = 0.6
    for _ in range(budget):
        if cur == 0:
            return True
        if time.monotonic() > deadline:
            break

        # Saturation: adding a cross-side edge never increases the cost.
        left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
        right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
        if left and right:
            added = False
            for _ in range(30):
                a = rng.choice(left)
                b = rng.choice(right)
                if b not in adj[a]:
                    adj[a].add(b)
                    adj[b].add(a)
                    added = True
                    break
            if added:
                cur = _cost(n, adj, D)
                continue

        # Degree-preserving swap: (a,b),(c,e) -> (a,e),(c,b).
        E = [(a, b) for a in range(n) if color[a] == 0 for b in adj[a]]
        if len(E) < 2:
            break
        (a, b), (c, e) = rng.sample(E, 2)
        if a == c or b == e or e in adj[a] or b in adj[c]:
            T = max(0.05, T * 0.999)
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(n, adj, D)
        if new <= cur or rng.random() < math.exp(-(new - cur) / T):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
        T = max(0.05, T * 0.998)
    return cur == 0


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
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])

    # Structured starting points (validated before use).
    for n_c, e_c in _candidates(d):
        if n_c > best[0] and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)

    base_n, base_e = best
    while time.monotonic() < deadline:
        adj = [set() for _ in range(base_n)]
        for u, v in base_e:
            adj[u].add(v)
            adj[v].add(u)
        color = _bipartition(base_n, adj)

        n = _add_vertex(base_n, adj, color, d, D, rng)
        ok = _repair(n, adj, color, d, D, rng, deadline, budget=1500)
        if ok:
            e = [(u, v) for u in range(n) for v in adj[u] if u < v]
            if lib.is_valid(n, e, d, D):
                base_n, base_e = n, e
                if n > best[0]:
                    best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
