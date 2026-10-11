import math
import random
import time

import lib


def _small(d, D):
    """Always-valid fallback graph."""
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    return lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2


def _candidates(N, rng):
    """Groups of order N as (m, k, r) for lib.semidirect_group(m, k, r); cyclic group first."""
    if N == 1:
        return [(1, 1, 0)]
    cyc = [(N, 1, 1)]
    others = []
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m == 1:
            others.append((1, k, 0))
            continue
        for r in range(2, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                others.append((m, k, r))
    rng.shuffle(others)
    return cyc + others[:11]


def _tables(m, k, r):
    N, mul, inv = lib.semidirect_group(m, k, r)
    Mt = [[mul(x, s) for s in range(N)] for x in range(N)]
    Iv = [inv(s) for s in range(N)]
    return N, Mt, Iv


def _bad(N, Mt, S, Si, D, src):
    """Number of vertices at distance > D from src in the Haar-type bipartite graph.

    A vertices are 0..N-1, B vertices are N..2N-1. A x ~ B (x*s) for s in S.
    """
    seen = [False] * (2 * N)
    seen[src] = True
    frontier = [src]
    reached = 1
    for _ in range(D):
        nxt = []
        for u in frontier:
            if u < N:
                row = Mt[u]
                for s in S:
                    v = N + row[s]
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            else:
                row = Mt[u - N]
                for si in Si:
                    v = row[si]
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
        if not nxt:
            break
        reached += len(nxt)
        frontier = nxt
    return 2 * N - reached


def _score(data, S, D):
    N, Mt, Iv = data
    Si = [Iv[s] for s in S]
    # Left multiplication is an automorphism, so vertex-transitive on each side:
    # checking eccentricity from A-identity and B-identity suffices.
    return _bad(N, Mt, S, Si, D, 0) + _bad(N, Mt, S, Si, D, N)


def _hill(data, d, D, steps, rng):
    N = data[0]
    S = rng.sample(range(N), d)
    cur = _score(data, S, D)
    for _ in range(steps):
        if cur == 0:
            break
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        S2 = S[:]
        S2[i] = t
        sc = _score(data, S2, D)
        if sc <= cur:
            S, cur = S2, sc
    return S if cur == 0 else None


def _try_order(N, d, D, rng, deadline):
    """Search for a valid Haar-type graph over a group of order N before deadline."""
    if N < d:
        return None
    groups = _candidates(N, rng)
    if not groups:
        return None
    data = {}
    while time.monotonic() < deadline:
        for gi, g in enumerate(groups):
            if time.monotonic() >= deadline:
                break
            if gi not in data:
                data[gi] = _tables(*g)
            S = _hill(data[gi], d, D, 200, rng)
            if S is not None:
                return data[gi][0], S, data[gi][1]
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.8 * time_limit - 1.0)
    rng = random.Random(seed)

    fallback = _small(d, D)
    best = fallback

    try:
        # D = 3 with d-1 a prime power: projective plane incidence graph meets the Moore bound.
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
            cand = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(cand[0], cand[1], d, D):
                return cand

        if d >= 2 and D >= 2:
            lo = d
            hi = max(d, lib.moore_bound(d, D) // 2)
            per_probe = max(1.0, 0.8 * time_limit / 9.0)
            while lo < hi and time.monotonic() < deadline - 0.2:
                mid = (lo + hi + 1) // 2
                now = time.monotonic()
                slice_end = min(deadline, now + per_probe)
                res = _try_order(mid, d, D, rng, slice_end)
                ok = False
                if res is not None:
                    N, S, Mt = res
                    edges = [(x, N + Mt[x][s]) for x in range(N) for s in S]
                    cand = (2 * N, edges)
                    if lib.is_valid(cand[0], cand[1], d, D):
                        best = cand
                        ok = True
                if ok:
                    lo = mid
                else:
                    hi = mid - 1
    except Exception:
        best = fallback

    if lib.is_valid(best[0], best[1], d, D):
        return best
    return fallback
