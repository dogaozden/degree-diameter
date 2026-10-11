import math
import random
import time

import numpy as np

import lib


# Idea: bi-Cayley graphs over non-abelian groups.
# A graph with parts A = {a_x} and B = {b_y}, indexed by a finite group G, and edges
# a_x -- b_{x*g} for g in S (|S| = d) is d-regular and bipartite. Left multiplication
# acts transitively on A and on B, so the diameter is at most D exactly when every
# vertex is within distance D of a_e and of b_e. That needs only two BFS runs, not
# all-pairs. We search over semidirect products Z_m x| Z_k (wider than the cyclic
# lifts the parent uses), and hill-climb on S to minimise the number of vertices
# left beyond distance D.

def _group_params(N):
    """All (m, k, r) with m*k = N, m >= 2, giving Z_m x|_r Z_k (k = 1 gives cyclic)."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """Right-multiplication table MG[g][x] = x*g and list of inverses for the semidirect group."""
    N = m * k
    x = np.arange(N, dtype=np.int64)
    A = x // k
    B = x % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    MG = np.empty((N, N), dtype=np.int64)
    for g in range(N):
        c, e = divmod(g, k)
        MG[g] = ((A + pw[B] * c) % m) * k + (B + e) % k
    pwl = [int(v) for v in pw]
    INV = []
    for g in range(N):
        c, e = divmod(g, k)
        nb = (-e) % k
        INV.append(((-pwl[nb] * c) % m) * k + nb)
    return MG.tolist(), INV


def _unreached(S, N, D, MG, INV):
    """Count vertices not within distance D of a_e or of b_e (0 means diameter <= D)."""
    nbA = [MG[g] for g in S]
    nbB = [MG[INV[g]] for g in S]
    total = 0
    for start in (0, N):
        seen = [False] * (2 * N)
        seen[start] = True
        frontier = [start]
        count = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    for Mg in nbA:
                        w = N + Mg[v]
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
                else:
                    y = v - N
                    for Mh in nbB:
                        w = Mh[y]
                        if not seen[w]:
                            seen[w] = True
                            nxt.append(w)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += 2 * N - count
    return total


def _climb(N, d, D, MG, INV, rng, deadline, iters):
    """Hill-climb over d-subsets S of the group, minimising the unreached count."""
    S = rng.sample(range(N), d)
    c = _unreached(S, N, D, MG, INV)
    it = 0
    while c and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(d)
        cur = set(S)
        g = rng.randrange(N)
        while g in cur:
            g = rng.randrange(N)
        T = list(S)
        T[i] = g
        c2 = _unreached(T, N, D, MG, INV)
        if c2 <= c:
            S, c = T, c2
    return S if c == 0 else None


def _attempt(N, d, D, rng, deadline):
    """Try to find a valid bi-Cayley graph on 2N vertices before the deadline."""
    params = _group_params(N)
    rng.shuffle(params)
    for m, k, r in params:
        if time.monotonic() >= deadline:
            break
        MG, INV = _tables(m, k, r)
        for _ in range(4):
            if time.monotonic() >= deadline:
                break
            S = _climb(N, d, D, MG, INV, rng, deadline, 600)
            if S is not None:
                edges = [(x, N + MG[g][x]) for g in S for x in range(N)]
                return 2 * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + max(0.5, 0.8 * time_limit - 1.0)

    # Calibration case: exact projective-plane incidence graph.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    if d >= 1 and D >= 2:
        fallback = lib.haar_graph(d, range(d))  # K_{d,d}, diameter 2
    elif d >= 1 and D >= 1:
        fallback = (2, [(0, 1)])
    else:
        return (1, [])
    if d < 2 or D < 2:
        return fallback

    best = fallback
    rng = random.Random(seed)
    lo, hi = 0, None
    N = max(d + 1, 40)

    # Ladder/bisection over group order N: the largest feasible order gives the best graph.
    while time.monotonic() < end - 0.2:
        now = time.monotonic()
        remaining = end - now
        budget = min(max(remaining / 3.0, 0.5), 12.0)
        sol = _attempt(N, d, D, rng, min(end, now + budget))
        if sol:
            n, edges = sol
            if n > best[0] and lib.is_valid(n, edges, d, D):
                best = (n, edges)
            lo = N
            if hi is not None and lo >= hi:
                hi = None
            if hi is None:
                N = int(N * 1.3) + 1
            else:
                N = (lo + hi) // 2
        else:
            hi = N if hi is None else min(hi, N)
            if lo + 1 < hi:
                N = max(lo + 1, (lo + hi) // 2)
            else:
                N = hi  # retry the boundary with fresh randomness

    n, edges = best
    if lib.is_valid(n, edges, d, D):
        return n, edges
    return fallback
