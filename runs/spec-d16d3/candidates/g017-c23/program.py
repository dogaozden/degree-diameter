import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Haar graphs from difference covers (diameter 3 family).
#
# H(m, S): vertices a_i = i and b_j = m + j (i, j in Z_m); a_i ~ b_j iff j - i in S.
# With |S| = d it is d-regular and bipartite. Using the translation and a<->b swap
# automorphisms, diameter <= D holds iff every vertex is within distance D of a_0.
# For D = 3 this reduces to two covering conditions:
#   (a) D1 = S - S covers all of Z_m   (a-a and b-b pairs, distance 2)
#   (b) D1 + S covers all of Z_m       (a-b pairs, distance 1 or 3)
# Order 2m beats 394 once m >= 198. The Moore bound caps m at d(d-1)+1 = 241.
# Simulated annealing on S (with 0 in S, WLOG) minimises the number of uncovered
# residues. For D != 3 it uses a BFS from a_0 instead.
# ----------------------------------------------------------------------------

def _cover_cost3(S, m):
    """Number of uncovered residues for H(m, S) at D = 3 (0 means diameter <= 3)."""
    diffs = (S[:, None] - S[None, :]) % m
    mark = np.zeros(m, dtype=bool)
    mark[diffs.ravel()] = True
    A2 = np.flatnonzero(mark)  # includes 0
    mark3 = np.zeros(m, dtype=bool)
    mark3[((A2[:, None] + S[None, :]) % m).ravel()] = True
    return int(m - A2.size) + int(m - mark3.sum())


def _cost_generic(S, m, D):
    """Vertices not reached from a_0 within distance D in H(m, S)."""
    N = 2 * m
    seen = bytearray(N)
    seen[0] = 1
    frontier = [0]
    count = 1
    for _ in range(D):
        nxt = []
        for v in frontier:
            if v < m:
                for s in S:
                    u = m + (v + s) % m
                    if not seen[u]:
                        seen[u] = 1
                        nxt.append(u)
            else:
                j = v - m
                for s in S:
                    u = (j - s) % m
                    if not seen[u]:
                        seen[u] = 1
                        nxt.append(u)
        count += len(nxt)
        frontier = nxt
        if not frontier:
            break
    return N - count


def _anneal(m, d, D, rng, iters, deadline, fast):
    """Anneal a connection set S (|S| = d, 0 in S) in Z_m so H(m, S) has diameter <= D."""
    T0, T1 = 1.5, 0.2
    S = [0] + rng.sample(range(1, m), d - 1)

    def cost(Sl):
        if fast:
            return _cover_cost3(np.array(Sl, dtype=np.int64), m)
        return _cost_generic(Sl, m, D)

    c = cost(S)
    for it in range(iters):
        if c == 0:
            break
        if (it & 1023) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(1, d)
        x = rng.randrange(1, m)
        if x in S:
            continue
        T_list = S[:]
        T_list[i] = x
        c2 = cost(T_list)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
            S, c = T_list, c2
    return S if c == 0 else None


def _haar_search(d, D, seed, deadline, consider):
    """Ascend m from d+1, annealing a valid connection set for each m, until a step fails."""
    rng = random.Random(seed * 1000003 + d * 31 + D)
    fast = (D == 3)
    m_cap = lib._moore_bound(d, D) // 2
    m = d + 1
    while time.monotonic() < deadline and m <= m_cap:
        found = None
        for _ in range(4):
            if time.monotonic() >= deadline:
                break
            found = _anneal(m, d, D, rng, 12000, deadline, fast)
            if found is not None:
                break
        if found is None:
            break
        n, e = lib.haar_graph(m, found)
        consider(n, e)
        m += 1


def _largest_prime_power_at_most(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 (valid for D >= 2).
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Incidence graph of PG(2, q) with q + 1 <= d (diameter 3).
    if D >= 3:
        q = _largest_prime_power_at_most(min(d - 1, 31))
        if q is not None:
            n, e = lib.projective_plane_incidence(q)
            consider(n, e)

    # Main new family: Haar graphs from difference covers, with annealing.
    if d >= 2:
        _haar_search(d, D, seed, start + 0.8 * time_limit, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
