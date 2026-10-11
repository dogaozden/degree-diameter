import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Construction: bipartite Cayley (group Haar) graphs over finite groups.
#
# For a group G of order N and a connection set S (|S| = d), let the graph have
# side-0 vertices (0, x) and side-1 vertices (1, y), with (0, x) ~ (1, x*s) for s in S.
# Left multiplication by h is an automorphism, so the graph is transitive on each side.
# Hence diameter <= D iff BFS from (0, e) and from (1, e) reaches everything within D.
#
# Groups are semidirect products Z_m x| Z_k (lib.semidirect_group), including cyclic
# groups (k = 1). S is found by simulated annealing on the number of unreached
# vertices. The group order N is found by binary search, and every returned graph
# is checked with lib.is_valid.
# ----------------------------------------------------------------------------


def _cost(S, MT, INV, N, D):
    """Number of (source, target) vertex pairs unreached within D steps, over both source sides."""
    total = 0
    for start in (0, 1):
        seen = [np.zeros(N, dtype=bool), np.zeros(N, dtype=bool)]
        F = np.zeros(N, dtype=bool)
        F[0] = True  # identity is element 0 in both lib encodings
        side = start
        seen[side][0] = True
        for _ in range(D):
            idx = np.flatnonzero(F)
            if idx.size == 0:
                break
            nxt = np.zeros(N, dtype=bool)
            if side == 0:
                for s in S:
                    nxt[MT[s][idx]] = True          # (0,x) -> (1, x*s)
            else:
                for s in S:
                    nxt[MT[INV[s]][idx]] = True     # (1,y) -> (0, y*s^-1)
            side ^= 1
            seen[side] |= nxt
            F = nxt
        total += 2 * N - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal(N, d, D, MT, INV, rng, deadline, iters):
    """Simulated annealing for a connection set S of d distinct group elements with cost 0."""
    S = rng.sample(range(N), d)
    inS = set(S)
    c = _cost(S, MT, INV, N, D)
    T = 1.0
    for it in range(iters):
        if c == 0:
            return S
        if (it & 127) == 0 and time.monotonic() > deadline:
            break
        i = rng.randrange(d)
        y = rng.randrange(N)
        if y in inS:
            continue
        old = S[i]
        S[i] = y
        c2 = _cost(S, MT, INV, N, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            inS.discard(old)
            inS.add(y)
            c = c2
        else:
            S[i] = old
        T = max(0.2, T * 0.998)
    return S if c == 0 else None


def _group_params(N):
    """Parameters (m, k, r) of semidirect products Z_m x| Z_k of order N; (N, 1, 1) is cyclic."""
    out = [(N, 1, 1)]
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


_TABLE_CACHE = {}


def _group_tables(m, k, r):
    """Return (MT, INV): MT[s][x] = x*s, INV[s] = s^-1, as numpy arrays."""
    key = (m, k, r)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    order, mul, _inv = lib.semidirect_group(m, k, r)
    M = np.empty((order, order), dtype=np.int64)
    for x in range(order):
        M[x] = [mul(x, s) for s in range(order)]
    MT = np.ascontiguousarray(M.T)
    INV = np.argmax(M == 0, axis=1)  # M[s, x] = s*x == e  ->  x = s^-1
    _TABLE_CACHE[key] = (MT, INV)
    return MT, INV


def _find_group(N, d, D, deadline, rng):
    """Try groups of order N with annealing until deadline. Returns (S, MT) or None."""
    params = _group_params(N)
    rng.shuffle(params)
    i = 0
    while time.monotonic() < deadline:
        m, k, r = params[i % len(params)]
        i += 1
        MT, INV = _group_tables(m, k, r)
        S = _anneal(N, d, D, MT, INV, rng, deadline, 3000)
        if S is not None:
            return S, MT
    return None


def _graph_from(N, S, MT):
    """Bipartite graph on 2N vertices: x (side 0) ~ N + x*s (side 1) for s in S."""
    edges = []
    for s in S:
        col = MT[s].tolist()
        for x in range(N):
            edges.append((x, N + col[x]))
    return 2 * N, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    end = start + 0.85 * T
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Calibration: incidence graph of PG(2, d-1) meets the Moore bound for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        consider(*lib.projective_plane_incidence(d - 1))
    if best[0] >= moore:
        return best

    # Binary search on the group order N for a valid bipartite Cayley graph of degree d.
    lo = max(d, best[0] // 2)
    hi = moore // 2 + 1
    while hi - lo > 1 and time.monotonic() < end - 0.5:
        mid = (lo + hi) // 2
        now = time.monotonic()
        probe_end = min(end, now + max(1.0, 0.22 * (end - now)))
        res = _find_group(mid, d, D, probe_end, rng)
        if res is not None:
            S, MT = res
            n, e = _graph_from(mid, S, MT)
            if lib.is_valid(n, e, d, D):
                consider(n, e)
                lo = mid
            else:
                hi = mid
        else:
            hi = mid

    return best
