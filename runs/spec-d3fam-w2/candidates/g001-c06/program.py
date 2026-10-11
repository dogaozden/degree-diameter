import random
import time

import lib


def _colors(n, edges):
    """2-colour the graph by BFS (one colour per component, arbitrary orientation)."""
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


def _alp_base(d, D):
    """Araujo-Pardo-Lopez record graph for d = q+2, q a prime power, D = 3."""
    q = d - 2
    if D != 3 or q < 3 or not lib.is_prime_power(q):
        return None
    try:
        n, edges = lib.araujo_lopez_graph(q)
    except Exception:
        return None
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return None


def _extend(d, D, n, edges, rng, deadline):
    """Randomised structural extension: each attempt adds one point P and one line L.

    Pick k pairwise-disjoint edges (pt_i, ln_i), delete them, then join P to every
    freed line ln_i, L to every freed point pt_i, and P to L. Degrees stay <= d
    (P and L get k+1 <= d), the graph stays bipartite, and the move is kept only if
    the diameter is still <= D. Returns the best valid (n, edges) found.
    """
    cur = [tuple(e) for e in edges]
    best = (n, list(cur))
    while time.monotonic() < deadline:
        col = _colors(n, cur)
        k = rng.randint(max(1, d - 3), d - 1)
        order = list(range(len(cur)))
        rng.shuffle(order)
        used_pts, used_lns = set(), set()
        removed = []
        for idx in order:
            u, v = cur[idx]
            pt, ln = (u, v) if col[u] == 0 else (v, u)
            if pt in used_pts or ln in used_lns:
                continue
            used_pts.add(pt)
            used_lns.add(ln)
            removed.append((idx, pt, ln))
            if len(removed) == k:
                break
        if len(removed) < k:
            continue

        rem = {idx for idx, _, _ in removed}
        P, L = n, n + 1
        new = [e for i, e in enumerate(cur) if i not in rem]
        new += [(P, ln) for _, _, ln in removed]
        new += [(pt, L) for _, pt, _ in removed]
        new.append((P, L))

        if lib.within_diameter(n + 2, new, D):
            cur = new
            n += 2
            best = (n, list(cur))
    return best


def _haar_search(d, D, seed, deadline):
    """Original fallback: random Haar graph search (always valid, weaker)."""
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
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
    deadline = start + 0.6 * time_limit
    q = d - 1

    # Calibration / exact constructions: instant and optimal.
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    fallback = (d, lib.haar_graph(d, range(d)))  # safe default, replaced below if possible
    rng = random.Random(seed)

    # Bold path for D = 3 when d-1 is not a prime power: start from the
    # Araujo-Pardo-Lopez record graph (every vertex degree d) and search for
    # extensions that add vertices while keeping diameter 3.
    base = _alp_base(d, D)
    if base is not None:
        n0, e0 = base
        best = (n0, e0)
        try:
            cand = _extend(d, D, n0, e0, rng, deadline)
            if cand[0] > n0 and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
        except Exception:
            best = (n0, e0)
        return best

    # Generic fallback for every other case.
    result = _haar_search(d, D, seed, start + 0.8 * time_limit)
    if lib.is_valid(result[0], result[1], d, D):
        return result
    return fallback[0], lib.haar_graph(d, range(d))[1] if False else lib.haar_graph(d, range(d))
