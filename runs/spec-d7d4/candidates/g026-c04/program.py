import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley (group-lift) graphs over non-abelian groups.
#
# For a finite group G of order M and a generating multiset S of size d with
# e in S, the graph with parts a_x, b_y (x, y in G) and edges a_x ~ b_{x*s}
# (s in S) is d-regular and bipartite on 2M vertices. Left multiplication by
# any h in G is an automorphism, so the diameter is <= D iff every vertex is
# within D of a_e and within D of b_e. Each check is two small BFS runs.
#
# The search tries groups Z_m x| Z_k (and cyclic groups) of increasing order M,
# runs simulated annealing over S, and keeps the largest verified graph.
# ----------------------------------------------------------------------------


def _groups(M):
    """Descriptors of groups of order M: cyclic, plus Z_m x|_r Z_k with m*k = M."""
    out = [("c", M, 1, 0)]
    for m in range(2, M):
        if M % m:
            continue
        k = M // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append(("s", m, k, r))
    return out


def _table(g, M):
    """Multiplication table T[x][y] and inverse list for the group described by g."""
    if g[0] == "c":
        _, mul, inv = lib.cyclic_group(M)
    else:
        _, mul, inv = lib.semidirect_group(g[1], g[2], g[3])
    T = [[mul(x, y) for y in range(M)] for x in range(M)]
    iv = [inv(x) for x in range(M)]
    return T, iv


def _cost(S, T, iv, N, D):
    """Number of (source, vertex) pairs not within D, for sources a_e and b_e."""
    Sinv = [iv[s] for s in S]
    tot = 2 * N
    adj = [None] * tot
    for x in range(N):
        row = T[x]
        adj[x] = [N + row[s] for s in S]
    for y in range(N):
        row = T[y]
        adj[N + y] = [row[si] for si in Sinv]
    total = 0
    for src in (0, N):
        seen = bytearray(tot)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                for u in adj[v]:
                    if not seen[u]:
                        seen[u] = 1
                        nxt.append(u)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += tot - cnt
    return total


def _sa(T, iv, N, d, D, end, rng):
    """Simulated annealing over shift sets S (containing e) of size d. Returns sorted S or None."""
    while time.monotonic() < end:
        S = [0] + rng.sample(range(1, N), d - 1)
        c = _cost(S, T, iv, N, D)
        temp = 1.0
        for it in range(6000):
            if c == 0:
                return sorted(S)
            if it % 20 == 0 and time.monotonic() >= end:
                return None
            k = rng.randrange(1, d)
            y = rng.randrange(1, N)
            if y in S:
                continue
            S2 = S[:]
            S2[k] = y
            c2 = _cost(S2, T, iv, N, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                S, c = S2, c2
                if c == 0:
                    return sorted(S)
            temp = max(0.25, temp * 0.999)
    return None


def _try_order(M, d, D, end, rng):
    """Search groups of order M for a valid shift set until `end`. Returns (group, S) or None."""
    groups = _groups(M)
    cache = {}
    while time.monotonic() < end:
        g = rng.choice(groups)
        if g not in cache:
            cache.clear()
            cache[g] = _table(g, M)
        T, iv = cache[g]
        run_end = min(end, time.monotonic() + 3.0)
        S = _sa(T, iv, M, d, D, run_end, rng)
        if S is not None:
            return g, S
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    T_lim = float(time_limit)
    deadline = t0 + max(0.5, min(0.85 * T_lim, T_lim - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best_n >= moore:
        return best_n, best_e

    hi = moore // 2  # group order M gives n = 2M <= moore
    M = d + 1
    fails = 0
    slice_len = max(2.0, 0.15 * T_lim)

    try:
        while M <= hi and time.monotonic() < deadline and fails < 2:
            end = min(deadline, time.monotonic() + slice_len)
            res = _try_order(M, d, D, end, rng)
            if res is None:
                fails += 1
                M += 1
                continue
            fails = 0
            g, S = res
            T, _ = _table(g, M)
            n = 2 * M
            e = [(x, M + T[x][s]) for x in range(M) for s in S]
            if n > best_n and lib.is_valid(n, e, d, D):
                best_n, best_e = n, e
            M += 1
    except Exception:
        pass

    return best_n, best_e
