import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Family: bi-Cayley graphs (k = 1) over affine groups F_q x| H, H <= F_q^*.
#
# Elements are maps x -> a*x + b with a in H (|H| = h) and b in F_q, so the
# group order is m = q*h. Vertices A_g and B_g for g in G, and the graph has
# A_g ~ B_{g*s} for each connection element s in S, |S| = d. Left
# multiplication by G is an automorphism that is transitive on each side,
# so the diameter is at most D iff the BFS from A_e and from B_e reaches
# every vertex within D steps. Searching S by annealing is a different
# search space from the parent's random semidirect voltages.
# ----------------------------------------------------------------------------

def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _prim_root(q):
    if q == 2:
        return 1
    fac = [p for p in range(2, q) if (q - 1) % p == 0 and _is_prime(p)]
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fac):
            return g
    return None


def _affine_group(q, h):
    """Return (m, mul, inv) for F_q x| H with H the subgroup of order h. Identity has index 0."""
    g = _prim_root(q)
    step = (q - 1) // h
    H = [pow(g, step * i, q) for i in range(h)]  # H[0] = 1
    pos = np.full(q, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    m = q * h
    aa = np.repeat(np.array(H, dtype=np.int64), q)   # index = ai*q + b
    bb = np.tile(np.arange(q, dtype=np.int64), h)
    pa = (aa[:, None] * aa[None, :]) % q
    pb = (aa[:, None] * bb[None, :] + bb[:, None]) % q  # (a1,b1)(a2,b2) = (a1a2, a1*b2 + b1)
    mul = pos[pa] * q + pb
    inv = np.empty(m, dtype=np.int64)
    for i in range(m):
        a = int(aa[i])
        b = int(bb[i])
        ai = pow(a, q - 2, q)
        bi = (-ai * b) % q
        inv[i] = int(pos[ai]) * q + bi
    return m, mul, inv


def _cost(S, mul, inv, m, D):
    """Total unreached (vertex, source) pairs from A_e and B_e within D steps. Zero iff valid."""
    Sa = np.asarray(S, dtype=np.int64)
    iS = inv[Sa]
    empty = np.empty(0, dtype=np.int64)
    total = 0
    for side in (0, 1):
        visA = np.zeros(m, dtype=bool)
        visB = np.zeros(m, dtype=bool)
        if side == 0:
            visA[0] = True
            fA = np.array([0], dtype=np.int64)
            fB = empty
        else:
            visB[0] = True
            fA = empty
            fB = np.array([0], dtype=np.int64)
        for _ in range(D):
            if fA.size == 0 and fB.size == 0:
                break
            nB = mul[np.ix_(fA, Sa)].ravel() if fA.size else empty
            nA = mul[np.ix_(fB, iS)].ravel() if fB.size else empty
            nB = np.unique(nB)
            nB = nB[~visB[nB]]
            nA = np.unique(nA)
            nA = nA[~visA[nA]]
            visB[nB] = True
            visA[nA] = True
            fA, fB = nA, nB
        total += 2 * m - int(visA.sum()) - int(visB.sum())
    return total


def _search_group(m, mul, inv, d, D, deadline, rng):
    """Annealed search with restarts for a connection set S of size d; returns S or None."""
    if m < d:
        return None
    while time.monotonic() < deadline:
        S = rng.sample(range(m), d)
        c = _cost(S, mul, inv, m, D)
        bestc = c
        stall = 0
        T = 1.0
        while c > 0 and stall < 4000 and time.monotonic() < deadline:
            stall += 1
            i = rng.randrange(d)
            x = rng.randrange(m)
            if x in S:
                continue
            S2 = S[:]
            S2[i] = x
            c2 = _cost(S2, mul, inv, m, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / T):
                S, c = S2, c2
                if c < bestc:
                    bestc = c
                    stall = 0
            T = max(0.05, T * 0.998)
        if c == 0:
            return S
    return None


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (degree q + 1 <= d)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.80 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 3 and d >= 2:
        moore = lib.moore_bound(d, D)
        if (d, D) == (6, 5):
            lo, hi = 342, 460
        else:
            lo = max(d, moore // 8)
            hi = max(lo, moore // 2)

        cands = []
        for q in range(2, hi + 1):
            if not _is_prime(q):
                continue
            for h in range(1, q):
                if (q - 1) % h:
                    continue
                m = q * h
                if lo <= m <= hi and m >= d:
                    cands.append((m, q, h))
        cands.sort()

        for idx, (m, q, h) in enumerate(cands):
            now = time.monotonic()
            if now >= deadline:
                break
            remaining = len(cands) - idx
            gd = now + (deadline - now) / remaining
            mm, mul, inv = _affine_group(q, h)
            S = _search_group(mm, mul, inv, d, D, gd, rng)
            if S is None:
                continue
            edges = []
            for s in S:
                col = mul[:, s].tolist()
                for g, b in enumerate(col):
                    edges.append((g, mm + int(b)))
            consider(2 * mm, edges)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
