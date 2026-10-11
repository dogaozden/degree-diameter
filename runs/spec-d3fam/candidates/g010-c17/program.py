import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (DFS from each unseen vertex)."""
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


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS over adjacency sets)."""
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
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _add(adj, a, b):
    adj[a].add(b)
    adj[b].add(a)


def _remove(adj, a, b):
    adj[a].discard(b)
    adj[b].discard(a)


def _attach_pair(n, edges, col, d, rng):
    """Degree-preserving insertion of a new colour-1 vertex P and colour-0 vertex L.

    A random matching of d edges (a, b), with a of colour 0, is replaced by (a, P) and (L, b).
    Old degrees are unchanged, P and L get degree d. Returns (n+2, adj, E) or None.
    """
    adj = [set() for _ in range(n + 2)]
    for u, v in edges:
        _add(adj, u, v)
    P, L = n, n + 1
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
        _remove(adj, a, b)
        _add(adj, a, P)
        _add(adj, b, L)
        E.append((a, P))
        E.append((L, b))
    return n + 2, adj, E


def _anneal(N, adj, E, col, d, D, rng, deadline):
    """Local search over bipartite graphs with max degree d on N fixed vertices.

    Moves (kept bipartite, degree <= d):
      - 2-switch of two edges (keeps all degrees),
      - add an edge between two vertices that both have spare degree,
      - delete an edge (creates spare degree that later add-moves can use).
    Cost = number of ordered pairs at distance > D. Metropolis acceptance with a
    temperature that decays linearly to 0.05 at the deadline.
    Mutates adj and E in place. Returns True when cost reaches 0, else False.
    """
    cur = _bad_count(N, adj, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return False
        T = max(0.05, 1.0 - (now - t0) / span)
        r = rng.random()
        if r < 0.7:
            M = len(E)
            if M < 2:
                return False
            i = rng.randrange(M)
            j = rng.randrange(M)
            if i == j:
                continue
            a, b = E[i]
            c, e = E[j]
            if a == c or b == e or e in adj[a] or b in adj[c]:
                continue
            _remove(adj, a, b)
            _remove(adj, c, e)
            _add(adj, a, e)
            _add(adj, c, b)
            new = _bad_count(N, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
                E[i] = (a, e)
                E[j] = (c, b)
            else:
                _remove(adj, a, e)
                _remove(adj, c, b)
                _add(adj, a, b)
                _add(adj, c, e)
        elif r < 0.85:
            s0 = [v for v in range(N) if col[v] == 0 and len(adj[v]) < d]
            s1 = [v for v in range(N) if col[v] == 1 and len(adj[v]) < d]
            if not s0 or not s1:
                continue
            a = rng.choice(s0)
            b = rng.choice(s1)
            if b in adj[a]:
                continue
            _add(adj, a, b)
            E.append((a, b))
            new = _bad_count(N, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
            else:
                _remove(adj, a, b)
                E.pop()
        else:
            M = len(E)
            if M == 0:
                continue
            i = rng.randrange(M)
            a, b = E[i]
            _remove(adj, a, b)
            new = _bad_count(N, adj, D)
            if new <= cur or rng.random() < math.exp((cur - new) / T):
                cur = new
                E[i] = E[-1]
                E.pop()
            else:
                _add(adj, a, b)
    return True


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add two vertices (a point and a line) and repair with _anneal.

    Each step starts from the previous valid graph, so the result is always valid
    (checked with lib.is_valid) and at least as large as the input.
    """
    cur_n, cur_edges = n, list(edges)
    adj0 = [set() for _ in range(n)]
    for u, v in cur_edges:
        _add(adj0, u, v)
    cur_col = _color(n, adj0)
    mb = _moore(d, D)
    while cur_n + 2 <= mb and time.monotonic() < deadline:
        att = _attach_pair(cur_n, cur_edges, cur_col, d, rng)
        if att is None:
            break
        N, adj, E = att
        colN = cur_col + [1, 0]
        if not _anneal(N, adj, E, colN, d, D, rng, deadline):
            break
        if not lib.is_valid(N, E, d, D):
            break
        cur_n, cur_edges, cur_col = N, list(E), colN
    return cur_n, cur_edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None and lib.is_valid(base[0], base[1], d, D):
        best = base
        if D == 3:
            try:
                res = _grow(base[0], base[1], d, D, rng, deadline)
                if res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
                    best = res
            except Exception:
                pass
        return best

    # Fallback: random Haar graphs.
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
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
