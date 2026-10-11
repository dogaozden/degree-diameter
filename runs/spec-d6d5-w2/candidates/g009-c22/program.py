import random
import time

import lib


def _cost(n, adj, D):
    """Ordered pairs at distance > D (bit-parallel). Zero iff connected with diameter <= D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _edge_list(adj, color):
    """Edges as (A, B) pairs, where A is colour 0 and B is colour 1."""
    return [(a, b) for a in range(len(adj)) if color[a] == 0 for b in adj[a]]


def _add_pair(adj, color, d, rng):
    """Add one new A vertex and one new B vertex, keeping the graph d-regular.

    Pick d vertex-disjoint edges (a_i, b_i). Delete them, join the new A vertex to
    all b_i and the new B vertex to all a_i. Returns False if no such matching exists.
    """
    E = _edge_list(adj, color)
    rng.shuffle(E)
    used = set()
    pick = []
    for a, b in E:
        if a in used or b in used:
            continue
        used.add(a)
        used.add(b)
        pick.append((a, b))
        if len(pick) == d:
            break
    if len(pick) < d:
        return False
    A = len(adj)
    B = A + 1
    color.append(0)
    color.append(1)
    adj.append(set())
    adj.append(set())
    for a, b in pick:
        adj[a].discard(b)
        adj[b].discard(a)
        adj[A].add(b)
        adj[b].add(A)
        adj[B].add(a)
        adj[a].add(B)
    return True


def _anneal(adj, E, D, deadline, rng, iters):
    """Degree-preserving double-edge swaps that reduce the bad-pair cost. Returns the final cost."""
    n = len(adj)
    cost = _cost(n, adj, D)
    it = 0
    while cost and it < iters and len(E) >= 2 and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(len(E))
        j = rng.randrange(len(E))
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
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
        if new <= cost or rng.random() < 0.02:
            cost = new
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
    return cost


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is d-regular.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n_c, e_c):
        nonlocal best, best_n
        if n_c > best_n and lib.is_valid(n_c, e_c, d, D):
            best = (n_c, e_c)
            best_n = n_c

    if D >= 3:
        # Cheap structured candidates.
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            try:
                consider(*lib.projective_plane_incidence(q))
            except Exception:
                pass
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(*lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D < 3:
        return best

    # Main family: grow a d-regular bipartite graph one vertex pair at a time from K_{d,d},
    # and after each growth step anneal the wiring toward diameter <= D.
    # Only valid states are committed to the output; invalid states are rolled back.
    adj = [set() for _ in range(2 * d)]
    color = [0] * d + [1] * d
    for a in range(d):
        for b in range(d, 2 * d):
            adj[a].add(b)
            adj[b].add(a)

    snap_adj = [set(s) for s in adj]
    snap_color = list(color)
    E = _edge_list(adj, color)
    cost = _cost(len(adj), adj, D)
    stagnant = 0
    shrink = 0

    while time.monotonic() < deadline:
        if cost == 0:
            n_cur = len(adj)
            if n_cur > best_n:
                consider(n_cur, _edge_list(adj, color))
            snap_adj = [set(s) for s in adj]
            snap_color = list(color)
            stagnant = 0
            step = max(1, (len(adj) // 25) >> shrink)
            for _ in range(step):
                if time.monotonic() >= deadline:
                    break
                if not _add_pair(adj, color, d, rng):
                    break
            E = _edge_list(adj, color)
            cost = _cost(len(adj), adj, D)
            continue

        cost = _anneal(adj, E, D, deadline, rng, 150)
        if cost:
            stagnant += 1
            if stagnant >= 8:
                # Stalled: roll back to the last valid graph and grow more gently.
                adj[:] = [set(s) for s in snap_adj]
                color[:] = snap_color
                shrink = min(shrink + 1, 5)
                E = _edge_list(adj, color)
                cost = 0
                stagnant = 0

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
