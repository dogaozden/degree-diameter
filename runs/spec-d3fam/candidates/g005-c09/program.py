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
    """Bitmask of vertices within distance D of each vertex."""
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


def _badv(n, adj, D):
    """Per-vertex count of vertices at distance > D."""
    return [n - r.bit_count() for r in _reach(n, adj, D)]


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _grow(n, edges, d, D, rng, deadline):
    """Add two vertices (point P, line L) and repair by focused 2-switches.

    Each step picks a vertex that still has a bad pair, and proposes a 2-switch on one
    of its incident edges together with a random edge elsewhere. Switches keep all
    degrees and bipartiteness. Annealing accepts moves on the total number of bad pairs.
    Returns (n+2, edges) with diameter <= D, or None on timeout.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1           # P has colour 1 (neighbours colour 0); L has colour 0
    adj.append(set())
    adj.append(set())
    N = n + 2
    adj[P]  # ensure exists

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
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
    col.append(1)   # P
    col.append(0)   # L

    pos = {e: i for i, e in enumerate(E)}
    M = len(E)

    def apply(i, j):
        """Switch E[i]=(x,y), E[j]=(z,w) into (x,w), (z,y)."""
        x, y = E[i]
        z, w = E[j]
        adj[x].discard(y); adj[y].discard(x)
        adj[z].discard(w); adj[w].discard(z)
        adj[x].add(w); adj[w].add(x)
        adj[z].add(y); adj[y].add(z)
        del pos[(x, y)]
        del pos[(z, w)]
        E[i] = (x, w)
        E[j] = (z, y)
        pos[(x, w)] = i
        pos[(z, y)] = j

    badv = _badv(N, adj, D)
    total = sum(badv)
    T = 2.0
    while total > 0:
        if time.monotonic() >= deadline:
            return None
        bl = [v for v in range(N) if badv[v] > 0]
        u = rng.choice(bl)
        w = rng.choice(list(adj[u]))
        e1 = (u, w) if col[u] == 0 else (w, u)
        i = pos[e1]
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        apply(i, j)
        nbad = _badv(N, adj, D)
        ntotal = sum(nbad)
        if ntotal <= total or rng.random() < math.exp(-(ntotal - total) / T):
            badv, total = nbad, ntotal
        else:
            apply(i, j)   # inverse switch restores the previous edges
        T = max(0.05, T * 0.9995)
    return N, list(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.7 * time_limit
    rng = random.Random(seed)

    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            mb = _moore(d, D)
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _grow(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs, always validated.
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
