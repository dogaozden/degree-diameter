import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Bi-Cayley graphs over finite groups.
#
# For a finite group G of order N and a set S of d elements containing the
# identity, put a_x ~ b_{x*s} for every x in G and s in S. The graph is
# d-regular and bipartite. Left multiplication by any group element is an
# automorphism, so the diameter is at most D iff every vertex is within D of
# a_e and within D of b_e. Each check is a BFS over 2N vertices.
#
# Groups are cyclic Z_N or semidirect products Z_m x| Z_k (lib.semidirect_group),
# which gives non-abelian options that cyclic Haar graphs cannot reach.
# Every candidate is checked with lib.is_valid before it replaces the best.
# ----------------------------------------------------------------------------


def _bfs_bad(N, M, S, Sinv, D, from_a):
    """Number of vertices not within distance D of a_e (from_a) or b_e (not from_a)."""
    total = 2 * N
    seen = bytearray(total)
    start = 0 if from_a else N
    seen[start] = 1
    frontier = [start]
    count = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < N:
                row = M[v]
                for s in S:
                    w = N + row[s]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            else:
                row = M[v - N]
                for t in Sinv:
                    w = row[t]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return total - count


def _cost(N, M, S, Sinv, D):
    return _bfs_bad(N, M, S, Sinv, D, True) + _bfs_bad(N, M, S, Sinv, D, False)


def _search_group(N, M, inv, d, D, deadline, rng):
    """Simulated annealing with restarts for a shift set S (identity included) of size d."""
    if d < 2 or N < d:
        return None
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, N), d - 1)
        Sinv = [inv[s] for s in S]
        c = _cost(N, M, S, Sinv, D)
        T = 1.0
        for it in range(1500):
            if c == 0:
                return sorted(S)
            if (it & 63) == 0 and time.monotonic() > deadline:
                return None
            k = rng.randrange(1, d)
            y = rng.randrange(1, N)
            if y in S:
                continue
            S2 = list(S)
            S2[k] = y
            Sinv2 = [inv[s] for s in S2]
            c2 = _cost(N, M, S2, Sinv2, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, Sinv, c = S2, Sinv2, c2
            T = max(0.15, T * 0.998)
    return None


def _inv_list(M, N):
    inv = [0] * N
    for x in range(N):
        row = M[x]
        for y in range(N):
            if row[y] == 0:
                inv[x] = y
                break
    return inv


def _groups_of_order(N, rng):
    """Cyclic group first, then semidirect products Z_m x| Z_k with m*k = N, k >= 2."""
    groups = [('cyc', N)]
    extra = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        rs = [r for r in range(1, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if not rs:
            continue
        if len(rs) > 4:
            rs = rng.sample(rs, 4)
        for r in rs:
            extra.append(('sd', m, k, r))
    rng.shuffle(extra)
    return groups + extra


def _make_group(spec):
    if spec[0] == 'cyc':
        return lib.cyclic_group(spec[1])
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


# ----------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.82 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Order N gives 2N vertices; N cannot exceed half the Moore bound.
    Nmax = moore // 2
    per = max(0.6, 0.06 * T)
    fails = 0
    N = max(d, 2)
    while N <= Nmax and time.monotonic() < deadline and fails < 6:
        found = None
        groups = _groups_of_order(N, rng)
        slot = per / max(1, len(groups))
        for spec in groups:
            now = time.monotonic()
            if now >= deadline:
                break
            end = min(deadline, now + max(0.25, slot))
            try:
                order, mul, _ = _make_group(spec)
                if order != N:
                    continue
                M = [[mul(x, y) for y in range(N)] for x in range(N)]
                inv = _inv_list(M, N)
                S = _search_group(N, M, inv, d, D, end, rng)
            except Exception:
                S = None
            if S is not None:
                found = (M, S)
                break
        if found is not None:
            M, S = found
            edges = []
            for x in range(N):
                row = M[x]
                for s in S:
                    edges.append((x, N + row[s]))
            consider(2 * N, edges)
            fails = 0
        else:
            fails += 1
        N += 1

    return best
