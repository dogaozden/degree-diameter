import math
import random
import time

import numpy as np
import lib


def _groups(N):
    """Parameters (m, k, r) of groups of order N: Z_m x|_r Z_k with r^k = 1 mod m (includes cyclic Z_N)."""
    out = []
    for m in range(1, N + 1):
        if N % m:
            continue
        k = N // m
        rs = range(m) if m > 1 else [0]
        for r in rs:
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _table(m, k, r):
    """Multiplication table M (N x N) and inverse array of Z_m x|_r Z_k, element (a, b) coded as a*k+b, identity 0."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    X = np.arange(N, dtype=np.int64)
    a = X // k
    b = X % k
    pa = (a[:, None] + pw[b][:, None] * a[None, :]) % m
    pb = (b[:, None] + b[None, :]) % k
    M = pa * k + pb
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return M, inv


def _score(M, inv, N, D, S):
    """Number of (source, target) vertex pairs at distance > D, from the two sources A_e and B_e.

    The bi-Cayley graph has A_g ~ B_{g s} (s in S). Left multiplication is an automorphism
    preserving both parts, so eccentricities of A_e and B_e determine the diameter.
    """
    Sarr = np.array(S, dtype=np.int64)
    Sinv = inv[Sarr]
    # Adjacency of the 2N vertices: A_g = g, B_h = N + h.
    Adj = np.concatenate([N + M[:, Sarr], M[:, Sinv]], axis=0)
    n2 = 2 * N
    total = 0
    for src in (0, N):
        vis = np.zeros(n2, dtype=bool)
        vis[src] = True
        fr = np.array([src], dtype=np.int64)
        for _ in range(D):
            if fr.size == 0:
                break
            mask = np.zeros(n2, dtype=bool)
            mask[Adj[fr].ravel()] = True
            mask &= ~vis
            vis |= mask
            fr = np.flatnonzero(mask)
        total += n2 - int(vis.sum())
    return total


def _search(M, inv, N, d, D, rng, t_end):
    """Simulated-annealing search over connection sets S (1 in S, |S| = d) with zero bad pairs."""
    while time.monotonic() < t_end:
        S = [0] + rng.sample(range(1, N), d - 1)
        f = _score(M, inv, N, D, S)
        bestf, stall, T = f, 0, 1.0
        while f > 0 and stall < 1500:
            if time.monotonic() >= t_end:
                return None
            j = rng.randrange(1, d)
            x = rng.randrange(1, N)
            if x in S:
                continue
            S2 = S[:]
            S2[j] = x
            f2 = _score(M, inv, N, D, S2)
            if f2 <= f or rng.random() < math.exp(-(f2 - f) / T):
                S, f = S2, f2
            if f < bestf:
                bestf, stall = f, 0
            else:
                stall += 1
            T = max(0.25, T * 0.997)
        if f == 0:
            return S
    return None


def _edges(M, S, N):
    edges = [(g, N + int(M[g, s])) for g in range(N) for s in S]
    return 2 * N, edges


def _attempt(N, d, D, rng, t_end):
    """Try to find a valid bi-Cayley graph on 2N vertices before t_end. Returns (n, edges) or None."""
    grs = _groups(N)
    if not grs:
        return None
    nonab = [g for g in grs if g[0] > 2 and g[2] != 1]
    while time.monotonic() < t_end:
        pool = nonab if (nonab and rng.random() < 0.75) else grs
        m, k, r = rng.choice(pool)
        M, inv = _table(m, k, r)
        now = time.monotonic()
        sub_end = min(t_end, now + max(0.2, (t_end - now) / 2))
        S = _search(M, inv, N, d, D, rng, sub_end)
        if S is not None:
            return _edges(M, S, N)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.7 * time_limit, time_limit - 3.0)
    deadline = start + max(0.0, budget)

    # Trivial cases.
    if D <= 0 or d <= 0:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        return n, [(i, (i + 1) % n) for i in range(n)]

    # Calibration: projective plane incidence graph (optimal for D = 3).
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)

    # Baseline: K_{d,d}, diameter 2, always valid.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    if D == 3 and d >= 5 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    try:
        rng = random.Random(seed)
        N = max(d + 1, best[0] // 2 + 1)
        fails = 0
        while time.monotonic() < deadline and fails < 5:
            now = time.monotonic()
            remaining = deadline - now
            slice_t = min(5.0, max(0.3, remaining / 8))
            res = _attempt(N, d, D, rng, min(deadline, now + slice_t))
            ok = False
            if res is not None:
                n, e = res
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
                    ok = True
                elif lib.is_valid(n, e, d, D):
                    ok = True
            fails = 0 if ok else fails + 1
            N += 1
    except Exception:
        pass

    return best
