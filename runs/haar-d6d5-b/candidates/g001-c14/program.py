import math
import random
import time

import lib


def _parent_search(d, D, seed, deadline):
    """Cyclic Haar random search from the parent program. Used as a safe fallback."""
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


def _descriptors(N, rng):
    """Group descriptors (m, k, r) with m*k == N, representing Z_m x|_r Z_k.
    (N, 1, 1) is the cyclic group Z_N."""
    out = [(N, 1, 1)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 3:
            continue
        rs = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1]
        rng.shuffle(rs)
        for r in rs[:3]:
            out.append((m, k, r))
    return out


def _table(desc):
    """Multiplication table and inverse table for the group described by desc.
    Element (a, b) is coded as a*k + b; (a,b)*(c,d) = (a + r^b c, b + d)."""
    m, k, r = desc
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    mt = []
    for x in range(N):
        a, b = divmod(x, k)
        pa = pw[b]
        row = [0] * N
        for y in range(N):
            c, e = divmod(y, k)
            row[y] = ((a + pa * c) % m) * k + (b + e) % k
        mt.append(row)
    inv = [0] * N
    for x in range(N):
        a, b = divmod(x, k)
        nb = (-b) % k
        inv[x] = ((-pw[nb] * a) % m) * k + nb
    return mt, inv


def _cost(S, mt, inv, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2. Zero cost means diameter <= 5."""
    P = {mt[inv[s]][t] for s in S for t in S}
    Pl = list(P)
    Q = set()
    for x in Pl:
        row = mt[x]
        for y in Pl:
            Q.add(row[y])
    P2 = {mt[s][inv[t]] for s in S for t in S}
    Pl2 = list(P2)
    Q2 = set()
    for x in Pl2:
        row = mt[x]
        for y in Pl2:
            Q2.add(row[y])
    return (N - len(Q)) + (N - len(Q2))


def _anneal(d, N, mt, inv, rng, t_end, K=6, T=0.6, patience=3000):
    """Search for S (identity fixed in S, d elements) with cost 0. Returns S or None."""
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, N), d - 1)
        cur = _cost(S, mt, inv, N)
        stall = 0
        while cur > 0 and stall < patience and time.monotonic() < t_end:
            inS = set(S)
            best_c, best_S = None, None
            for _ in range(K):
                i = rng.randrange(1, d)
                x = rng.randrange(1, N)
                if x in inS:
                    continue
                cand = S[:]
                cand[i] = x
                c = _cost(cand, mt, inv, N)
                if best_c is None or c < best_c:
                    best_c, best_S = c, cand
            if best_S is None:
                stall += 1
                continue
            if best_c <= cur or rng.random() < math.exp(-(best_c - cur) / T):
                if best_c < cur:
                    stall = 0
                else:
                    stall += 1
                cur = best_c
                S = best_S
            else:
                stall += 1
        if cur == 0:
            return S
    return None


def _haar_from(mt, S, N):
    """Haar-type graph: A-vertex g joins B-vertex N + s*g for each s in S."""
    edges = [(g, N + mt[s][g]) for s in S for g in range(N)]
    return 2 * N, edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 5.0))
    deadline = t0 + budget

    if d <= 0 or D <= 0:
        return 1, []
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    if D == 1:
        fallback = (2, [(0, 1)])
    else:
        fallback = lib.haar_graph(d, range(d))

    if D != 5:
        n, edges = _parent_search(d, D, seed, deadline)
        if lib.is_valid(n, edges, d, D):
            return n, edges
        return fallback

    # D == 5: safe cyclic parent phase first, then non-abelian Haar ladder.
    best_n, best_edges = fallback
    n, edges = _parent_search(d, D, seed, t0 + 0.15 * budget)
    if n > best_n and lib.is_valid(n, edges, d, D):
        best_n, best_edges = n, edges

    rng = random.Random(seed)
    N_t = max(d, best_n // 2) + 1
    cache = {}
    cache_N = None
    descs = []
    slice_t = 0.4
    while time.monotonic() < deadline:
        N = N_t
        if N != cache_N:
            cache = {}
            cache_N = N
            descs = _descriptors(N, rng)
        found = None
        for desc in descs:
            now = time.monotonic()
            if now >= deadline:
                break
            if desc not in cache:
                cache[desc] = _table(desc)
            mt, inv = cache[desc]
            S = _anneal(d, N, mt, inv, rng, min(deadline, now + slice_t))
            if S is not None:
                cn, ce = _haar_from(mt, S, N)
                if lib.is_valid(cn, ce, d, D):
                    found = (cn, ce)
                    break
        if found:
            best_n, best_edges = found
            N_t += 1
            slice_t = 0.4
        else:
            slice_t *= 1.5

    if lib.is_valid(best_n, best_edges, d, D):
        return best_n, best_edges
    return fallback
