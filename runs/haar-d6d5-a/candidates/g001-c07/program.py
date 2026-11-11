import math
import random
import time

import lib


def _cyclic_search(d, D, rng, deadline):
    """Random search over cyclic Haar graphs (the parent's method), used as a quick fallback."""
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


def _groups_of_order(N):
    """All metacyclic groups Z_m x|_r Z_k with m*k = N (r = 1 gives the cyclic-type lift)."""
    out = []
    for m in range(2, N + 1):
        if N % m:
            continue
        k = N // m
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(N, m, k, r):
    _, mul, inv = lib.semidirect_group(m, k, r)
    M = [[mul(x, y) for y in range(N)] for x in range(N)]
    I = [inv(x) for x in range(N)]
    return M, I


def _cost(S, M, I, N):
    """Uncovered group elements in (S^-1 S)^2 and (S S^-1)^2; zero means diameter <= 5."""
    Sinv = [I[s] for s in S]
    A = {M[a][b] for a in Sinv for b in S}
    B = {M[a][b] for a in S for b in Sinv}
    A2 = {M[x][y] for x in A for y in A}
    B2 = {M[x][y] for x in B for y in B}
    return (N - len(A2)) + (N - len(B2))


def _anneal(N, M, I, d, rng, t_end):
    S = rng.sample(range(N), d)
    cur = _cost(S, M, I, N)
    best_c, stall, T = cur, 0, 0.8
    while cur > 0 and time.monotonic() < t_end:
        i = rng.randrange(d)
        x = rng.randrange(N)
        if x in S:
            continue
        S2 = S[:]
        S2[i] = x
        c2 = _cost(S2, M, I, N)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            S, cur = S2, c2
        if cur < best_c:
            best_c, stall = cur, 0
        else:
            stall += 1
            if stall > 1500:
                S = rng.sample(range(N), d)
                cur = _cost(S, M, I, N)
                best_c, stall = cur, 0
    return S if cur == 0 else None


def _group_haar(N, M, S):
    """Bipartite graph on 2N vertices: A-vertex g is g, B-vertex h is N + h; g ~ s*g."""
    edges = [(g, N + M[s][g]) for g in range(N) for s in S]
    return 2 * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    if D != 5 or d < 3:
        return _cyclic_search(d, D, rng, deadline)

    # Quick cyclic fallback first, so a valid graph is always available.
    best = _cyclic_search(d, D, rng, start + 0.15 * time_limit)
    lo = best[0] // 2

    group_list = {}
    slice_len = 2.0
    i = 0
    while time.monotonic() < deadline - 0.5:
        cands = list(range(max(342, lo + 1), 421))
        if not cands:
            break
        N = cands[i % len(cands)]
        i += 1
        if N not in group_list:
            group_list[N] = _groups_of_order(N)
        groups = group_list[N]
        if not groups:
            continue
        m, k, r = groups[rng.randrange(len(groups))]
        try:
            M, I = _tables(N, m, k, r)
        except ValueError:
            continue
        t_end = min(deadline, time.monotonic() + slice_len)
        S = _anneal(N, M, I, d, rng, t_end)
        if S is None:
            continue
        n, edges = _group_haar(N, M, S)
        if lib.is_valid(n, edges, d, D):
            best = (n, edges)
            lo = N

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
