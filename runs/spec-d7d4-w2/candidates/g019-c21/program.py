import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley graphs over small non-cyclic groups.
#
# Group G of order N (semidirect Z_m x| Z_k, cyclic when k = 1). Connection set
# S of d distinct elements. Vertices A_x and B_y (x, y in G) with A_x ~ B_{x*s}.
# Every such graph is d-regular and bipartite on 2N vertices. Left multiplication
# is an automorphism, so the diameter is <= D iff BFS from A_e and B_e reaches
# everything within D steps. A hill-climb over S minimises the number of
# unreached vertices. Orders N are tried in increasing order.
# ----------------------------------------------------------------------------


def _pg_base(d):
    """Projective-plane incidence graph for the largest prime power q <= d-1 (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _groups(N):
    """All semidirect groups Z_m x| Z_k of order N, as (m, k, r) triples."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _bad(S, MT, INV, N, D):
    """Number of vertices not within distance D of A_0 or of B_0 (0 means diameter <= D)."""
    adj = [None] * (2 * N)
    for x in range(N):
        row = MT[x]
        adj[x] = [N + row[s] for s in S]          # A_x -> B_{x s}
    for y in range(N):
        row = MT[y]
        adj[N + y] = [row[INV[s]] for s in S]     # B_y -> A_{y s^{-1}}
    bad = 0
    for src in (0, N):
        seen = [False] * (2 * N)
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = True
                        nxt.append(u)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        bad += 2 * N - count
    return bad


def _climb(N, d, D, MT, INV, rng, deadline, steps=1500):
    """Random restarts plus plateau-friendly hill-climbing on S. Returns S or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = _bad(S, MT, INV, N, D)
        for _ in range(steps):
            if cur == 0:
                return S
            i = rng.randrange(d)
            g = rng.randrange(N)
            if g in S:
                continue
            T = S[:]
            T[i] = g
            val = _bad(T, MT, INV, N, D)
            if val <= cur or rng.random() < 0.01:
                S, cur = T, val
        if cur == 0:
            return S
        if time.monotonic() >= deadline:
            break
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    end = start + min(0.85 * T, T - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 2:
        return best
    if d == 2:
        consider(2 * D, [(i, (i + 1) % (2 * D)) for i in range(2 * D)])
        return best

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    if D == 3:
        base = _pg_base(d)
        if base is not None:
            consider(base[0], base[1])
        if best[0] >= moore:
            return best

    # Bi-Cayley search: orders N = |G| with n = 2N, from just above the current best upward.
    Nlo = max(d, best[0] // 2 + 1)
    Nhi = moore // 2
    fails = 0
    N = Nlo
    while N <= Nhi and time.monotonic() < end and fails < 6:
        groups = _groups(N)
        rng.shuffle(groups)
        remaining = end - time.monotonic()
        t_end = time.monotonic() + max(0.5, 0.25 * remaining)
        found = None
        MT = INV = None
        gi = 0
        while found is None and time.monotonic() < t_end and groups:
            m, k, r = groups[gi % len(groups)]
            gi += 1
            _, mul, inv = lib.semidirect_group(m, k, r)
            MT = [[mul(x, y) for y in range(N)] for x in range(N)]
            INV = [inv(x) for x in range(N)]
            found = _climb(N, d, D, MT, INV, rng, t_end)
        if found is not None:
            edges = [(x, N + MT[x][s]) for x in range(N) for s in found]
            consider(2 * N, edges)
            fails = 0
        else:
            fails += 1
        N += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
