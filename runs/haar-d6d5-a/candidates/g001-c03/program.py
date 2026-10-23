import math
import random
import time
import lib


def _semidirect_tables(m, k, r):
    """Multiplication and inverse tables for Z_m x| Z_k (element (a, b) coded as a*k + b, r^k = 1 mod m)."""
    N = m * k
    pw = [pow(r, b, m) for b in range(k)]
    dm = [divmod(x, k) for x in range(N)]
    M = []
    for x in range(N):
        a, b = dm[x]
        pb = pw[b]
        M.append([((a + pb * c) % m) * k + (b + e) % k for c, e in dm])
    I = []
    for x in range(N):
        a, b = dm[x]
        nb = (-b) % k
        I.append(((-pw[nb] * a) % m) * k + nb)
    return N, M, I


def _groups(lo, hi):
    """Non-abelian metacyclic groups Z_m x| Z_k with order in [lo, hi], as (N, m, k, r)."""
    out = []
    for k in range(2, 30):
        for m in range(max(2, lo // k), hi // k + 1):
            N = m * k
            if N < lo or N > hi:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    out.append((N, m, k, r))
    return out


def _cost(S, M, I, N):
    """Uncovered elements of (S^-1 S)^2 and (S S^-1)^2; zero iff the Haar graph has diameter <= 5."""
    D1 = {M[I[s]][t] for s in S for t in S}
    Q1 = {M[x][y] for x in D1 for y in D1}
    D2 = {M[s][I[t]] for s in S for t in S}
    Q2 = {M[x][y] for x in D2 for y in D2}
    return 2 * N - len(Q1) - len(Q2)


def _anneal(N, M, I, d, rng, steps, deadline):
    """Simulated annealing over connection sets S of size d containing the identity."""
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _cost(S, M, I, N)
    best_c, best_S = cur, list(S)
    for step in range(steps):
        if cur == 0:
            break
        if (step & 255) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(1, d)
        g = rng.randrange(N)
        if g in S:
            continue
        old = S[i]
        S[i] = g
        c = _cost(S, M, I, N)
        T = 0.3 + 1.5 * (1.0 - step / steps)
        if c <= cur or rng.random() < math.exp((cur - c) / T):
            cur = c
            if c < best_c:
                best_c, best_S = c, list(S)
        else:
            S[i] = old
    return best_c, best_S


def _haar_edges(N, M, S):
    """Haar graph: A-vertex g is joined to B-vertex N + s*g for each s in S."""
    edges = []
    for g in range(N):
        for s in S:
            edges.append((g, N + M[s][g]))
    return 2 * N, edges


def _search_group(d, D, rng, deadline, best):
    pool = _groups(343, 420)
    while time.monotonic() < deadline:
        cand = [g for g in pool if 2 * g[0] > best[0]]
        if not cand:
            break
        N, m, k, r = rng.choice(cand)
        N, M, I = _semidirect_tables(m, k, r)
        bc, bS = _anneal(N, M, I, d, rng, 20000, deadline)
        if bc == 0:
            n, edges = _haar_edges(N, M, bS)
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
    return best


def _cyclic(d, D, rng, deadline, best):
    """Random cyclic Haar graphs (the parent's search), kept as a fallback."""
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
            if found[0] > best[0]:
                best = found
            misses = 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid
    if d == 6 and D == 5:
        # Short cyclic fallback, then non-abelian group search for the record-beating orders.
        best = _cyclic(d, D, rng, start + 0.1 * time_limit, best)
        best = _search_group(d, D, rng, deadline, best)
    else:
        best = _cyclic(d, D, rng, deadline, best)

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return lib.haar_graph(d, range(d))
