import random
import time
import lib


def _colors(n, edges):
    """2-colour a bipartite graph by BFS. Returns a list of 0/1 per vertex."""
    adj = lib.adjacency(n, edges)
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


def _augment(n, edges, d, D, seed, deadline):
    """Randomised greedy growth: repeatedly try to add a new (point, line) pair
    that uses spare degree on existing vertices. Every candidate is checked with
    lib.is_valid, so the result is always valid. Returns the best (n, edges) found."""
    rng = random.Random(seed)
    col = _colors(n, edges)
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    edges = list(edges)
    while time.monotonic() < deadline:
        A = [v for v in range(n) if col[v] == 0 and deg[v] < d]
        B = [v for v in range(n) if col[v] == 1 and deg[v] < d]
        if not A or not B:
            break
        ka = min(d - 1, len(B))
        kb = min(d - 1, len(A))
        SA = rng.sample(B, ka)   # new colour-0 vertex a joins these colour-1 vertices
        SB = rng.sample(A, kb)   # new colour-1 vertex b joins these colour-0 vertices
        a, b = n, n + 1
        new = [(a, b)] + [(a, x) for x in SA] + [(b, y) for y in SB]
        cand = edges + new
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            col.extend([0, 1])
            deg.extend([ka + 1, kb + 1])
            for x in SA:
                deg[x] += 1
            for y in SB:
                deg[y] += 1
    return n, edges


def _haar_fallback(d, D, seed, deadline):
    """Parent's randomised cyclic Haar search, used only when no algebraic construction applies."""
    rng = random.Random(seed)
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
    deadline = start + 0.75 * time_limit
    best = None

    if D == 3:
        # Candidate 1: Araujo-Pardo & Lopez graph for degree d = q + 2, order 2(q^2+q+5).
        q = d - 2
        if q >= 3 and lib.is_prime_power(q):
            try:
                n, e = lib.araujo_lopez_graph(q)
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
            except Exception:
                pass
        # Candidate 2: projective plane incidence graph for d - 1 = q, order 2(q^2+q+1).
        q = d - 1
        if q >= 2 and lib.is_prime_power(q):
            try:
                n, e = lib.projective_plane_incidence(q)
                if lib.is_valid(n, e, d, D) and (best is None or n > best[0]):
                    best = (n, e)
            except Exception:
                pass

    if best is None:
        try:
            best = _haar_fallback(d, D, seed, start + 0.8 * time_limit)
        except Exception:
            best = None

    if best is None or not lib.is_valid(best[0], best[1], d, D):
        return 1, []  # trivially valid fallback

    # Spend the remaining budget trying to grow the algebraic graph beyond its record.
    if D == 3:
        try:
            n, e = _augment(best[0], best[1], d, D, seed,
                            start + 0.85 * time_limit)
            if lib.is_valid(n, e, d, D) and n >= best[0]:
                best = (n, e)
        except Exception:
            pass

    return best
