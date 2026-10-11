import math
import random
import time

import lib


def _two_colour(n, edges):
    """Return a proper 2-colouring (list of 0/1) of a bipartite graph on n vertices."""
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


def _extend_pair(n, edges, d, D, rng, deadline, max_moves):
    """Add one point and one line to a d-regular bipartite graph of diameter <= D.

    Choose a matching M of k = d-1 edges (a_i, b_i). Delete them, then join the new
    point A to every b_i, the new line B to every a_i, and A to B. Every old vertex keeps
    its degree and A, B get degree d. Simulated annealing over the matching minimises
    lib.bad_pairs. Returns (n+2, edges) on success, else None.
    """
    col = _two_colour(n, edges)
    arcs = [(u, v) if col[u] == 0 else (v, u) for u, v in edges]
    k = d - 1
    if k < 1 or len(arcs) < k:
        return None
    A, B = n, n + 1

    order = list(range(len(arcs)))
    rng.shuffle(order)
    ua, ub, M = set(), set(), []
    for i in order:
        a, b = arcs[i]
        if a in ua or b in ub:
            continue
        ua.add(a)
        ub.add(b)
        M.append(i)
        if len(M) == k:
            break
    if len(M) < k:
        return None

    def build_edges(sel):
        removed = set(sel)
        out = [arcs[i] for i in range(len(arcs)) if i not in removed]
        for i in sel:
            a, b = arcs[i]
            out.append((A, b))
            out.append((B, a))
        out.append((A, B))
        return out

    cur = lib.bad_pairs(n + 2, build_edges(M), D)
    inM = set(M)
    moves = 0
    while cur > 0 and moves < max_moves and time.monotonic() < deadline:
        moves += 1
        j = rng.randrange(k)
        cand = rng.randrange(len(arcs))
        if cand in inM:
            continue
        a, b = arcs[cand]
        clash = False
        for t in range(k):
            if t != j and (arcs[M[t]][0] == a or arcs[M[t]][1] == b):
                clash = True
                break
        if clash:
            continue
        trial = M[:]
        trial[j] = cand
        c = lib.bad_pairs(n + 2, build_edges(trial), D)
        delta = c - cur
        T = 0.3 + 1.5 * (1 - moves / max_moves)
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            inM.discard(M[j])
            inM.add(cand)
            M = trial
            cur = c

    if cur != 0:
        return None
    return n + 2, build_edges(M)


def _grow(n, edges, d, D, rng, deadline):
    """Repeatedly add point/line pairs while the graph stays valid."""
    best = (n, edges)
    fails = 0
    while time.monotonic() < deadline and fails < 3 and n + 2 <= lib.moore_bound(d, D):
        res = _extend_pair(n, edges, d, D, rng, deadline, 2500)
        if res is None:
            fails += 1
            continue
        n2, e2 = res
        if not lib.is_valid(n2, e2, d, D):
            fails += 1
            continue
        n, edges = n2, e2
        best = (n, edges)
        fails = 0
    return best


def _haar_search(d, D, rng, deadline):
    """Fallback: random Haar graphs of growing order, keeping the largest valid one."""
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
    rng = random.Random(seed)

    if D == 3:
        base = None
        try:
            if lib.is_prime_power(d - 1):
                base = lib.projective_plane_incidence(d - 1)
            elif d - 2 >= 3 and lib.is_prime_power(d - 2):
                base = lib.araujo_lopez_graph(d - 2)
        except Exception:
            base = None
        if base is not None and lib.is_valid(base[0], base[1], d, D):
            n, edges = _grow(base[0], base[1], d, D, rng, deadline)
            if lib.is_valid(n, edges, d, D):
                return n, edges

    n, edges = _haar_search(d, D, rng, deadline)
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return 2, [(0, 1)]
