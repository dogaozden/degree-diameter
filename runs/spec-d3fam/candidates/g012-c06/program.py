import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Base constructions (safe fallbacks).
# ----------------------------------------------------------------------------

def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_base(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Bold step: vertex insertion followed by annealed edge rewiring.
#
# The graph stays bipartite because the side of every vertex is fixed and every
# edge is always oriented left -> right. A rewire move removes one edge (a, b)
# and adds (a2, b2), keeping all degrees <= d. Cost = number of vertex pairs at
# distance > D. Metropolis acceptance on that cost drives the search to zero.
# ----------------------------------------------------------------------------

def _colors(n, edges):
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


def _bad(n, adj, D):
    """Number of unordered vertex pairs at distance > D, via bitmask balls."""
    ball = [1 << v for v in range(n)]
    for _ in range(D):
        nxt = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            nxt.append(x)
        ball = nxt
    return sum(n - b.bit_count() for b in ball) // 2


def _add_pair(n, edges, color, d, rng):
    """Append one new left vertex v and one new right vertex w, attached to spare vertices."""
    v, w = n, n + 1
    E = list(edges)
    deg = [0] * (n + 2)
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
    rights = [x for x in range(n) if color[x] == 1 and deg[x] < d]
    lefts = [x for x in range(n) if color[x] == 0 and deg[x] < d]
    rng.shuffle(rights)
    rng.shuffle(lefts)
    E.append((v, w))
    deg[v] += 1
    deg[w] += 1
    for x in rights[:d - 1]:
        E.append((v, x))
        deg[v] += 1
        deg[x] += 1
    for x in lefts[:d - 1]:
        E.append((x, w))
        deg[w] += 1
        deg[x] += 1
    color2 = list(color) + [0, 1]
    return n + 2, E, color2


def _improve(n, edges, color, d, D, deadline, rng):
    """Annealed rewiring. Returns (True, edge_list) if all pairs are within distance D."""
    adj = [set() for _ in range(n)]
    E = []
    for u, v in edges:
        a, b = (u, v) if color[u] == 0 else (v, u)
        if b in adj[a]:
            continue
        adj[a].add(b)
        adj[b].add(a)
        E.append([a, b])
    deg = [len(s) for s in adj]
    if any(x > d for x in deg) or not E:
        return False, None

    left = [v for v in range(n) if color[v] == 0]
    right = [v for v in range(n) if color[v] == 1]

    # Greedy saturation with random attempts.
    for _ in range(40 * n):
        a = rng.choice(left)
        b = rng.choice(right)
        if deg[a] >= d or deg[b] >= d or b in adj[a]:
            continue
        adj[a].add(b)
        adj[b].add(a)
        deg[a] += 1
        deg[b] += 1
        E.append([a, b])

    cost = _bad(n, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        T = 2.0 * (0.02 ** ((now - t0) / span))
        i = rng.randrange(len(E))
        a, b = E[i]
        a2 = rng.choice(left)
        b2 = rng.choice(right)
        if a2 == a and b2 == b:
            continue
        if b2 in adj[a2]:
            continue
        if deg[a2] - (1 if a2 == a else 0) >= d:
            continue
        if deg[b2] - (1 if b2 == b else 0) >= d:
            continue

        # Apply move.
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a2].add(b2)
        adj[b2].add(a2)
        deg[a] -= 1
        deg[b] -= 1
        deg[a2] += 1
        deg[b2] += 1

        new = _bad(n, adj, D)
        delta = new - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            E[i] = [a2, b2]
            cost = new
        else:
            # Revert move.
            adj[a2].discard(b2)
            adj[b2].discard(a2)
            adj[a].add(b)
            adj[b].add(a)
            deg[a2] -= 1
            deg[b2] -= 1
            deg[a] += 1
            deg[b] += 1

    if cost == 0:
        return True, [(a, b) for a, b in E]
    return False, None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 10.0)
    deadline = start + max(budget, 1.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if D >= 3:
        cand = _araujo_base(d)
        if cand is not None:
            consider(cand[0], cand[1])
        cand = _pg_base(d)
        if cand is not None:
            consider(cand[0], cand[1])

    # Bold search: grow by vertex pairs, repair with annealing, keep what passes.
    cur_n, cur_e = best_n, best_e
    while time.monotonic() < deadline:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_end = time.monotonic() + max(3.0, remaining / 2.0)
        slice_end = min(slice_end, deadline)

        color = _colors(cur_n, cur_e)
        n2, e2, c2 = _add_pair(cur_n, cur_e, color, d, rng)
        ok, E = _improve(n2, e2, c2, d, D, slice_end, rng)
        if ok and lib.is_valid(n2, E, d, D):
            cur_n, cur_e = n2, E
            if n2 > best_n:
                best_n, best_e = n2, E
        else:
            # Restart from the best known graph with a fresh random state.
            cur_n, cur_e = best_n, best_e

    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = lib.haar_graph(d, range(d))
    return best_n, [tuple(e) for e in best_e]
