import math
import random
import time

import numpy as np

import lib


def _max_order(d):
    return 1 + d * (d - 1) + d * (d - 1) ** 3


def _candidates(hi, lo):
    """Yield (N, m, k, r) for semidirect products Z_m x| Z_k (r != 1, so non-abelian), N in [lo, hi], largest N first."""
    for N in range(hi, lo - 1, -1):
        for k in (2, 3, 4, 5, 6, 8, 10, 12):
            if N % k or N // k < 3:
                continue
            m = N // k
            got = 0
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1:
                    yield N, m, k, r
                    got += 1
                    if got == 2:
                        break


def _semidirect_tables(m, k, r):
    """Multiplication table and inverses for Z_m x| Z_k, element (a, b) coded a*k+b, (a,b)*(c,d) = (a + r^b c, b + d)."""
    N = m * k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int32)
    x = np.arange(N, dtype=np.int32)
    A = (x // k)[:, None]
    B = (x % k)[:, None]
    Ay = (x // k)[None, :]
    By = (x % k)[None, :]
    M = (((A + pw[B] * Ay) % m) * k + (B + By) % k).astype(np.int32)
    inv = np.argmax(M == 0, axis=1).astype(np.int32)
    return M, inv


def _cost(M, inv, S, N):
    """Uncovered elements of (S^-1 S)^2 plus uncovered elements of (S S^-1)^2. Zero means diameter <= 5."""
    Si = inv[S]
    D1 = M[Si[:, None], S[None, :]].ravel()   # s^-1 t
    D2 = M[S[:, None], Si[None, :]].ravel()   # s t^-1
    c = 0
    for D in (D1, D2):
        D = np.unique(D)
        P = M[D[:, None], D[None, :]].ravel()
        cov = np.zeros(N, dtype=bool)
        cov[P] = True
        c += N - int(cov.sum())
    return c


def _anneal(M, inv, N, d, rng, deadline):
    """Simulated annealing over d-element connection sets. Returns a zero-cost set or None."""
    while time.monotonic() < deadline:
        S = np.array(rng.sample(range(N), d), dtype=np.int32)
        cur = _cost(M, inv, S, N)
        best = cur
        stall = 0
        while stall < 3000 and time.monotonic() < deadline:
            if cur == 0:
                return S
            i = rng.randrange(d)
            x = rng.randrange(N)
            if x in S:
                continue
            T2 = S.copy()
            T2[i] = x
            c2 = _cost(M, inv, T2, N)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / 0.5):
                S, cur = T2, c2
            if cur < best:
                best, stall = cur, 0
            else:
                stall += 1
    return None


def _graph_from_set(M, S, N):
    """Haar-type graph: A-vertex g is g, B-vertex g is N+g, A_g ~ B_{s*g} for s in S."""
    edges = []
    for s in S.tolist():
        row = M[s].tolist()
        edges.extend((g, N + row[g]) for g in range(N))
    return 2 * N, edges


def _cyclic_search(d, D, rng, deadline, best):
    """Parent's cyclic Haar search, used as the fallback for other cases."""
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    group_deadline = start + 0.55 * time_limit
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    q = d - 1
    if D == 3 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid fallback

    if D == 5:
        try:
            hi = min(_max_order(d), 2200)
            lo = min(710, hi)
            for N, m, k, r in _candidates(hi, lo):
                now = time.monotonic()
                if now >= group_deadline:
                    break
                M, inv = _semidirect_tables(m, k, r)
                gdead = min(group_deadline, now + 2.5)
                S = _anneal(M, inv, N, d, rng, gdead)
                if S is None:
                    continue
                n, edges = _graph_from_set(M, S, N)
                if lib.is_valid(n, edges, d, D) and n > best[0]:
                    return n, edges
        except Exception:
            pass

    return _cyclic_search(d, D, rng, deadline, best)
