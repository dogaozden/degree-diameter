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


def _reach(n, adj, D):
    """Bitmask per vertex of all vertices within distance D."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _bad_total(n, reach):
    """Ordered count of pairs at distance > D from the reach masks."""
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


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (point P, line L) by degree-preserving switches.

    New helper: targeted switching. Each step picks a vertex x that still has a
    far vertex y (distance > D). It then prefers 2-switches that touch the
    neighbourhood of x on one edge and the neighbourhood of y on the other, so
    the move can bring x and y closer. A small fraction of moves is uniform
    random, to keep exploring. Acceptance is simulated annealing with cyclic
    reheating on the ordered bad-pair count.
    Returns (n+2, edges) with diameter <= D, or None on failure or timeout.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1          # P has colour 1 (neighbours colour 0); L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]  # (col0, col1)
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
    reach = _reach(N, adj, D)
    cur = _bad_total(N, reach)
    step = 0
    T0 = 1.5
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        step += 1
        # Cyclic reheating: temperature decays, then jumps back up.
        T = max(0.05, T0 * (0.9995 ** (step % 4000)))

        bad = [v for v in range(N) if reach[v].bit_count() < N]
        x = rng.choice(bad)
        rx = reach[x]
        far = [y for y in range(N) if y != x and not (rx >> y) & 1]
        y = rng.choice(far)

        if rng.random() < 0.2:
            i = rng.randrange(M)
            j = rng.randrange(M)
        else:
            Sx = adj[x] | {x}
            Sy = adj[y] | {y}
            ci = [k for k, (a, b) in enumerate(E) if a in Sx or b in Sx]
            cj = [k for k, (a, b) in enumerate(E) if a in Sy or b in Sy]
            if not ci or not cj:
                i = rng.randrange(M)
                j = rng.randrange(M)
            else:
                i = rng.choice(ci)
                j = rng.choice(cj)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue

        # 2-switch: (a,b),(c,e) -> (a,e),(c,b). Orientation stays (col0, col1).
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new_reach = _reach(N, adj, D)
        new = _bad_total(N, new_reach)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            reach = new_reach
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                try:
                    res = _augment(cur[0], cur[1], d, D, rng, deadline)
                except Exception:
                    res = None
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))          # K_{d,d}: always valid
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
