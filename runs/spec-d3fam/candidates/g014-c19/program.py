import math
import random
import time

import lib


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


def _adj_from(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    return adj


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
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def _bipartite_base(d, D):
    """Parent's structured D=3 base (record-level, used as the safe fallback)."""
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def _attach(n, col, E, d, rng):
    """Add a point P (colour 1) and a line L (colour 0), each of degree exactly d.

    Each new vertex takes neighbours from vertices with spare degree where possible.
    Any shortfall is covered by removing disjoint edges (a, b) and rewiring them to
    (a, P) and (L, b), which keeps all old degrees unchanged.
    Returns (n+2, colour list, edge list) or None.
    """
    deg = [0] * n
    for a, b in E:
        deg[a] += 1
        deg[b] += 1
    free0 = [v for v in range(n) if col[v] == 0 and deg[v] < d]
    free1 = [v for v in range(n) if col[v] == 1 and deg[v] < d]
    rng.shuffle(free0)
    rng.shuffle(free1)
    r = max(0, d - min(len(free0), len(free1)))
    if r > len(E):
        return None

    removal, used = [], set()
    if r:
        order = list(range(len(E)))
        rng.shuffle(order)
        for i in order:
            a, b = E[i]
            if a in used or b in used:
                continue
            removal.append(i)
            used.add(a)
            used.add(b)
            if len(removal) == r:
                break
        if len(removal) < r:
            return None

    s0 = [v for v in free0 if v not in used][: d - r]
    s1 = [v for v in free1 if v not in used][: d - r]
    if len(s0) < d - r or len(s1) < d - r:
        return None

    P, L = n, n + 1
    rem = set(removal)
    new = [E[i] for i in range(len(E)) if i not in rem]
    for i in removal:
        a, b = E[i]
        new.append((a, P))
        new.append((L, b))
    new.extend((x, P) for x in s0)
    new.extend((L, y) for y in s1)
    return n + 2, col + [1, 0], new


def _anneal(N, col, E, d, D, rng, deadline):
    """Repair diameter with degree-preserving 2-switches and spare-degree edge additions.

    Returns a valid edge list (diameter <= D) or None if the deadline hits first.
    """
    T = 1.0
    adj = _adj_from(N, E)
    E = list(E)
    deg = [len(s) for s in adj]
    cur = _bad_count(N, adj, D)
    while cur > 0:
        if time.monotonic() >= deadline:
            return None

        if rng.random() < 0.25:
            f0 = [v for v in range(N) if col[v] == 0 and deg[v] < d]
            f1 = [v for v in range(N) if col[v] == 1 and deg[v] < d]
            if not f0 or not f1:
                continue
            a = rng.choice(f0)
            b = rng.choice(f1)
            if b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            deg[a] += 1
            deg[b] += 1
            new = _bad_count(N, adj, D)
            if new <= cur:
                E.append((a, b))
                cur = new
            else:
                adj[a].discard(b)
                adj[b].discard(a)
                deg[a] -= 1
                deg[b] -= 1
            continue

        M = len(E)
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
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
    return E


def _grow(n, col, E, d, D, mb, rng, deadline):
    """Repeatedly attach a (point, line) pair and repair diameter; keep the last valid state."""
    while n + 2 <= mb and time.monotonic() < deadline:
        att = _attach(n, col, E, d, rng)
        if att is None:
            break
        N, col2, E2 = att
        res = _anneal(N, col2, E2, d, D, rng, deadline)
        if res is None:
            break
        n, col, E = N, col2, res
    return n, E


def _haar_search(d, D, rng, deadline):
    """Parent's fallback: random Haar graphs. Starts from K_{d,d}."""
    best = lib.haar_graph(d, range(d))
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)
    best = None

    # Safe fallback: parent's structured base (record-level for these D=3 cases).
    base = _bipartite_base(d, D)
    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base

    # Bold path for D=3: start from PG(2, q) with q the largest prime power <= d-1,
    # which has spare degree, then grow by attaching point/line pairs and annealing.
    if D == 3 and d >= 3:
        q = _largest_prime_power_at_most(d - 1)
        if q is not None and q >= 2:
            n0, e0 = lib.projective_plane_incidence(q)
            if lib.is_valid(n0, e0, d, D):
                col = _color(n0, _adj_from(n0, e0))
                E = [(u, v) if col[u] == 0 else (v, u) for u, v in e0]
                mb = _moore(d, D)
                n1, E1 = _grow(n0, col, E, d, D, mb, rng, deadline)
                cand = (n1, [(a, b) for a, b in E1])
                if ((best is None or cand[0] > best[0])
                        and lib.is_valid(cand[0], cand[1], d, D)):
                    best = cand

    # Non-D=3 cases (or no structured base): parent's random Haar fallback.
    if best is None:
        best = _haar_search(d, D, rng, deadline)

    # Final guard: always return a valid graph.
    if best is None or not lib.is_valid(best[0], best[1], d, D):
        if d >= 1 and D >= 1:
            return 2, [(0, 1)]
        return 1, []
    return best
