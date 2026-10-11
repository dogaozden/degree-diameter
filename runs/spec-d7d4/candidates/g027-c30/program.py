import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bold change: bi-Cayley / voltage lifts over NON-cyclic groups.
#
# A base graph with k vertices per side and an integer matrix C (row and column
# sums d) is lifted over a finite group G of order N:
#     a^i_x ~ b^j_{x*g}   for every g in V[i][j], |V[i][j]| = C[i][j],
# giving 2*k*N vertices, bipartite and d-regular. Left multiplication is an
# automorphism, so the diameter is <= D iff every one of the 2k base vertices
# reaches all vertices within D steps. Voltages are searched by simulated
# annealing with numpy BFS. Groups are cyclic or semidirect products Z_m x| Z_k.
#
# Every candidate is checked with lib.is_valid before it can replace the best.
# The fallback K_{d,d} is always valid for D >= 2. Cases with D = 3 and d-1 a
# prime power return the projective-plane incidence graph (the Moore graph).
# The legacy pipeline is dropped, so non-target cases may score lower.
# ----------------------------------------------------------------------------

_NCAP = 400        # largest group order tried
_PER_GROUP = 1.2   # seconds of annealing per group
_MAX_GROUPS = 3    # groups tried per (k, N)


def _matrix(k, d):
    """Base multiplicity matrix with all row and column sums equal to d."""
    if k == 1:
        return [[d]]
    if k == 2:
        x = d // 2
        return [[x, d - x], [d - x, x]]
    if k == 3:
        base, rem = divmod(d, 3)
        p = base + (1 if rem > 0 else 0)
        q = base + (1 if rem > 1 else 0)
        r = base
        C = [[0] * 3 for _ in range(3)]
        for i in range(3):
            C[i][i] = p
            C[i][(i + 1) % 3] = q
            C[i][(i + 2) % 3] = r
        return C
    return None


def _group_specs(N, rng):
    """Cyclic group plus a few random semidirect products Z_m x| Z_k of order N."""
    extra = []
    for m in range(2, N):
        if N % m:
            continue
        k = N // m
        if k < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                extra.append(("semi", m, k, r))
    rng.shuffle(extra)
    return [("cyc",)] + extra[:_MAX_GROUPS - 1]


def _triple(N, spec):
    if spec[0] == "cyc":
        return lib.cyclic_group(N)
    _, m, k, r = spec
    return lib.semidirect_group(m, k, r)


def _table(triple):
    """RM[g][x] = x*g, RMi[g][x] = x*g^{-1}, as numpy arrays."""
    N, mul, inv = triple
    MUL = np.array([[mul(x, y) for y in range(N)] for x in range(N)], dtype=np.int64)
    INV = np.array([inv(x) for x in range(N)], dtype=np.int64)
    RM = np.ascontiguousarray(MUL.T)
    RMi = RM[INV]
    return RM, RMi


def _cost(V, k, N, D, RM, RMi):
    """Total number of (source, target) pairs at distance > D over the 2k base sources."""
    total = 0
    full = 2 * k * N
    for side in (0, 1):
        for layer in range(k):
            seen = (np.zeros((k, N), dtype=bool), np.zeros((k, N), dtype=bool))
            F = np.zeros((k, N), dtype=bool)
            F[layer, 0] = True
            seen[side][layer, 0] = True
            cur = side
            for _ in range(D):
                NF = np.zeros((k, N), dtype=bool)
                if cur == 0:
                    for i in range(k):
                        idx = np.flatnonzero(F[i])
                        if idx.size == 0:
                            continue
                        for j in range(k):
                            for g in V[i][j]:
                                NF[j, RM[g][idx]] = True
                else:
                    for j in range(k):
                        idx = np.flatnonzero(F[j])
                        if idx.size == 0:
                            continue
                        for i in range(k):
                            for g in V[i][j]:
                                NF[i, RMi[g][idx]] = True
                nxt = 1 - cur
                NF &= ~seen[nxt]
                seen[nxt] |= NF
                F = NF
                cur = nxt
                if not F.any():
                    break
            total += full - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal(k, C, N, D, RM, RMi, deadline, rng):
    """Search voltages V[i][j] (distinct elements) with cost 0; returns V or None."""
    V = [[rng.sample(range(N), C[i][j]) if C[i][j] else [] for j in range(k)]
         for i in range(k)]
    cells = [(i, j) for i in range(k) for j in range(k) if C[i][j]]
    c = _cost(V, k, N, D, RM, RMi)
    T = 2.0
    while c and time.monotonic() < deadline:
        i, j = cells[rng.randrange(len(cells))]
        lst = V[i][j]
        p = rng.randrange(len(lst))
        new = rng.randrange(N)
        if new in lst:
            continue
        old = lst[p]
        lst[p] = new
        c2 = _cost(V, k, N, D, RM, RMi)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            c = c2
        else:
            lst[p] = old
        T = max(0.25, T * 0.9997)
    return V if c == 0 else None


def _lift(V, k, N, RM):
    """Edge list of the lift: a^i_x = i*N+x, b^j_y = k*N + j*N + y."""
    edges = []
    xs = np.arange(N, dtype=np.int64)
    for i in range(k):
        for j in range(k):
            for g in V[i][j]:
                us = (i * N + xs).tolist()
                ws = (k * N + j * N + RM[g]).tolist()
                edges.extend(zip(us, ws))
    return 2 * k * N, edges


def _attempt(k, N, d, D, deadline, rng):
    C = _matrix(k, d)
    if C is None or N < max(d, 2):
        return None
    for spec in _group_specs(N, rng):
        now = time.monotonic()
        if now >= deadline:
            break
        RM, RMi = _table(_triple(N, spec))
        sub = min(deadline, now + _PER_GROUP)
        V = _anneal(k, C, N, D, RM, RMi, sub, rng)
        if V is not None:
            n, edges = _lift(V, k, N, RM)
            if lib.is_valid(n, edges, d, D):
                return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    T = float(time_limit)
    deadline = start + 0.85 * T - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    M = lib._moore_bound(d, D)
    if best[0] >= M:
        return best

    # Moore graph for D = 3 when d - 1 is a prime power.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        try:
            n, e = lib.projective_plane_incidence(d - 1)
            if lib.is_valid(n, e, d, D):
                return n, e
        except Exception:
            pass

    # Search ladder: ascending total order, over k layers and group orders N.
    start_total = int(0.6 * M)
    max_total = min(M, 2 * _NCAP * 3)
    configs = []
    for k in (1, 2, 3):
        for N in range(1, _NCAP + 1):
            total = 2 * k * N
            if start_total <= total <= max_total:
                configs.append((total, k, N))
    configs.sort()

    for total, k, N in configs:
        if time.monotonic() >= deadline:
            break
        if total <= best[0]:
            continue
        try:
            res = _attempt(k, N, d, D, deadline, rng)
        except Exception:
            res = None
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res

    return best
