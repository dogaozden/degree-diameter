import math
import random
import time

import lib


def _fallback(d, D):
    """Always-valid small graph: K_{d,d} for D >= 2, a single edge for D = 1, a point for D = 0."""
    if d <= 0 or D <= 0:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))


def _group_options(N, rng):
    """(m, k, r) triples giving semidirect groups Z_m x| Z_k of order N = m*k (r = 1 is always included)."""
    opts = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        rs = [1]
        if m > 2:
            cand = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
            rng.shuffle(cand)
            rs += cand[:4]
        for r in rs:
            opts.append((m, k, r))
    return opts


def _bfs_reaches_all(adj, src, n, D):
    """True if every vertex is within distance D of src."""
    dist = [False] * n
    dist[src] = True
    frontier = [src]
    seen = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            for v in adj[u]:
                if not dist[v]:
                    dist[v] = True
                    nxt.append(v)
        seen += len(nxt)
        frontier = nxt
        if seen == n:
            return True
        if not frontier:
            break
    return seen == n


def _try_bicayley(N, m, k, r, d, D, rng):
    """Bi-Cayley graph on a group G of order N: A = G, B = G, x ~ y whenever y = x*s for s in S, |S| = d.

    Left translation by G is an automorphism, so G acts transitively on each side and
    two BFS runs (from A-identity and B-identity) decide the diameter.
    Returns the adjacency lists (vertices: A = 0..N-1, B = N..2N-1) when diameter <= D, else None.
    """
    _, mul, inv = lib.semidirect_group(m, k, r)
    S = rng.sample(range(N), d)
    Sinv = [inv(s) for s in S]
    n = 2 * N
    adj = [None] * n
    for x in range(N):
        adj[x] = [N + mul(x, s) for s in S]
    for y in range(N):
        adj[N + y] = [mul(y, t) for t in Sinv]
    if not _bfs_reaches_all(adj, 0, n, D):
        return None
    if not _bfs_reaches_all(adj, N, n, D):
        return None
    return adj


def _edges_from_adj(N, adj):
    return [(x, v) for x in range(N) for v in adj[x]]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.55 * time_limit, time_limit - 10.0))
    deadline = start + budget

    fb_n, fb_edges = _fallback(d, D)
    if not lib.is_valid(fb_n, fb_edges, d, D):
        fb_n, fb_edges = 1, []
    best_n, best_edges = fb_n, fb_edges

    # D = 3 with d-1 a prime power: projective plane incidence is Moore-optimal.
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        pn, pe = lib.projective_plane_incidence(q)
        if lib.is_valid(pn, pe, d, D):
            return pn, pe

    if d < 1 or D < 2:
        return best_n, best_edges

    rng = random.Random(seed)
    Nmax = lib.moore_bound(d, D) // 2
    best_N = best_n // 2 if best_n > 1 else 0

    N = max(d + 1, 2)
    fails = 0
    FAIL_LIMIT = 10
    TRIALS = 300

    while N <= Nmax and time.monotonic() < deadline and fails < FAIL_LIMIT:
        groups = _group_options(N, rng)
        found = None
        trials = 0
        while (trials < TRIALS and found is None
               and time.monotonic() < deadline and groups):
            trials += 1
            m, k, r = rng.choice(groups)
            adj = _try_bicayley(N, m, k, r, d, D, rng)
            if adj is not None:
                found = (N, adj)
        if found is not None:
            fN, adj = found
            edges = _edges_from_adj(fN, adj)
            n = 2 * fN
            if n > best_n and lib.is_valid(n, edges, d, D):
                best_n, best_edges = n, edges
                best_N = fN
            fails = 0
        else:
            fails += 1
        N += 1

    if lib.is_valid(best_n, best_edges, d, D):
        return best_n, best_edges
    return fb_n, fb_edges
