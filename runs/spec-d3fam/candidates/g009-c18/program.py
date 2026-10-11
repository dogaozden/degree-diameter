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
    """Ordered count of vertex pairs at distance > D (bitmask BFS from adjacency sets)."""
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


def _augment(n, edges, d, D, rng, deadline):
    """Add two vertices (a point P and a line L) by degree-preserving 2-switches with annealing."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

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

    M = len(E)
    cur = _bad_count(N, adj, D)
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


# ---------------------------------------------------------------- Haar search (bold branch)
#
# Haar graph H(m, S): a_i ~ b_{i+s} for s in S, S a d-subset of Z_m. It is bipartite, d-regular
# and order 2m. The map x -> x + t acts on each side, and a_i <-> b_{-i} swaps the sides, so
# diameter <= 3 holds iff  (S-S) covers Z_m  and  (S-S)+S covers Z_m.
# The cost below counts the uncovered residues; zero cost means diameter 3.

def _haar_cost(m, S):
    diffs = {(s - t) % m for s in S for t in S}
    d3 = {(x + s) % m for x in diffs for s in S}
    return (m - len(diffs)) + (m - len(d3))


def _haar_search(m, d, rng, deadline):
    """Anneal a d-subset of Z_m to zero cost. Returns the subset or None at the deadline."""
    S = rng.sample(range(m), d)
    cur = _haar_cost(m, S)
    T = 2.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(d)
        y = rng.randrange(m)
        if y in S:
            continue
        cand = S[:]
        cand[i] = y
        new = _haar_cost(m, cand)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            S, cur = cand, new
        T = max(0.05, T * 0.9995)
    return S


def _safe_base(d, D):
    """Structured record base for D = 3, or None."""
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)
    mb = _moore(d, D)

    # Structured base. The PG(2,q) incidence graph is Moore-optimal, so return it directly.
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)
        if lib.is_valid(base[0], base[1], d, D):
            return base

    best = None
    try:
        base = _safe_base(d, D)
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            best = base
    except Exception:
        best = None

    # Bold branch: Haar graphs of Z_m with a searched connection set, aiming above the base order.
    if D == 3 and d >= 3:
        m = max(d + 1, (best[0] // 2 + 1) if best is not None else d + 1)
        while time.monotonic() < deadline and m <= mb // 2:
            remaining = deadline - time.monotonic()
            attempt_deadline = time.monotonic() + max(0.5, 0.5 * remaining)
            S = _haar_search(m, d, rng, min(deadline, attempt_deadline))
            if S is None:
                break
            n, edges = lib.haar_graph(m, S)
            if lib.is_valid(n, edges, d, D) and (best is None or n > best[0]):
                best = (n, edges)
            m += 1

    # Augment the best structured base with the parent's 2-switch annealing, if time remains.
    if D == 3 and best is not None:
        cur = best
        while time.monotonic() < deadline and cur[0] + 2 <= mb:
            res = _augment(cur[0], cur[1], d, D, rng, deadline)
            if res is None or not lib.is_valid(res[0], res[1], d, D):
                break
            cur = res
        if cur[0] > best[0] and lib.is_valid(cur[0], cur[1], d, D):
            best = cur

    if best is not None:
        return best

    # General fallback: K_{d,d}, then random Haar graphs with growing m.
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
