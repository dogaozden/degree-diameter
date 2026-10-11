import math
import random
import time

import numpy as np

import lib


def _reach(R, S_arr, Sinv_arr, N, D, side0):
    """Vertices reached within D steps from the identity on side side0 (0 = A, 1 = B)."""
    visA = np.zeros(N, dtype=bool)
    visB = np.zeros(N, dtype=bool)
    if side0 == 0:
        visA[0] = True
    else:
        visB[0] = True
    cur = np.zeros(1, dtype=np.int64)
    side = side0
    for _ in range(D):
        if side == 0:
            # A_x is adjacent to B_{x*s} for s in S.
            nb = R[cur[:, None], S_arr[None, :]].ravel()
            nb = nb[~visB[nb]]
            visB[nb] = True
        else:
            # B_y is adjacent to A_{y*s^-1} for s in S.
            nb = R[cur[:, None], Sinv_arr[None, :]].ravel()
            nb = nb[~visA[nb]]
            visA[nb] = True
        side ^= 1
        if nb.size == 0:
            break
        cur = np.unique(nb)
    return visA, visB


def _cost(R, Ginv, S, N, D):
    """Number of (vertex, target) pairs beyond distance D, checked from A_e and B_e.

    The lift is invariant under left multiplication on each side, so cost 0 means
    diameter <= D for the whole graph.
    """
    S_arr = np.array(S, dtype=np.int64)
    Sinv_arr = Ginv[S_arr]
    visA, visB = _reach(R, S_arr, Sinv_arr, N, D, 0)
    c = (N - int(visA.sum())) + (N - int(visB.sum()))
    _, visB2 = _reach(R, S_arr, Sinv_arr, N, D, 1)
    c += N - int(visB2.sum())
    return c


def _search(R, Ginv, N, d, D, t_end, rng):
    """Local search for a connection set S of size d in a group of order N with cost 0."""
    if N == d:
        return list(range(N))
    S = [0] + rng.sample(range(1, N), d - 1)
    c = _cost(R, Ginv, S, N, D)
    best_c = c
    stall = 0
    while c > 0:
        if time.monotonic() >= t_end:
            return None
        stall += 1
        if stall > 600:
            # Restart from a fresh random set after a long plateau.
            S = [0] + rng.sample(range(1, N), d - 1)
            c = _cost(R, Ginv, S, N, D)
            best_c = c
            stall = 0
            continue
        pos = rng.randrange(1, d)
        new = rng.randrange(1, N)
        if new in S:
            continue
        S2 = S[:]
        S2[pos] = new
        c2 = _cost(R, Ginv, S2, N, D)
        if c2 <= c or rng.random() < 0.02:
            S, c = S2, c2
            if c < best_c:
                best_c = c
                stall = 0
    return S


def _group_descs(N):
    """Descriptions of groups of order N: cyclic, and Z_m x|_r Z_k with m*k = N."""
    out = [("cyc", N)]
    for k in range(2, N + 1):
        if N % k:
            continue
        m = N // k
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                out.append(("sd", m, k, r))
    return out


def _attempt(d, D, N, rng, t_end):
    """Try to build a valid bi-Cayley lift over some group of order N. Return (n, edges) or None."""
    if N < d:
        return None
    groups = _group_descs(N)
    rng.shuffle(groups)
    groups = groups[:6]
    for idx, desc in enumerate(groups):
        now = time.monotonic()
        if now >= t_end:
            break
        g_end = now + (t_end - now) / (len(groups) - idx)
        if desc[0] == "cyc":
            _, mul, inv = lib.cyclic_group(desc[1])
        else:
            _, mul, inv = lib.semidirect_group(desc[1], desc[2], desc[3])
        R = np.array([[mul(x, s) for s in range(N)] for x in range(N)], dtype=np.int64)
        Ginv = np.array([inv(s) for s in range(N)], dtype=np.int64)
        S = _search(R, Ginv, N, d, D, g_end, rng)
        if S is None:
            continue
        # Edges: A_x -- B_{x*s} for s in S. Vertices A_x = x, B_y = N + y.
        edges = [(x, N + int(R[x, s])) for x in range(N) for s in S]
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            return n, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.85 * time_limit, time_limit - 6.0)
    budget = max(budget, 0.3 * time_limit)
    deadline = start + budget

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    # Safe fallback: K_{d,d} if valid, else a single vertex (always valid).
    best = (1, [])
    try:
        base = lib.haar_graph(d, range(d))
        if lib.is_valid(base[0], base[1], d, D):
            best = base
    except Exception:
        pass

    if d < 2 or D < 2:
        return best

    lo = d if best[0] == 2 * d else 1
    rng = random.Random(seed)
    hi = None
    try:
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            if hi is None:
                N = lo + max(1, lo // 12)
            elif hi - lo <= 1:
                # Heuristic search may have missed; retry the frontier with fresh randomness.
                hi = None
                N = lo + 1
            else:
                N = (lo + hi) // 2
            slice_len = max(0.5, min(remaining, 0.15 * budget))
            t_end = min(deadline, now + slice_len)
            try:
                res = _attempt(d, D, N, rng, t_end)
            except Exception:
                res = None
            if res is not None:
                lo = N
                best = res
            else:
                if hi is None or N < hi:
                    hi = N
    except Exception:
        pass

    return best
