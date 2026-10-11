import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Groups as multiplication tables.
#
# A group is returned as (order, mul, ident): mul[i, j] is the index of
# element i times element j, and ident is the index of the identity.
# ----------------------------------------------------------------------------

def _psl2(p):
    """Return (order, mul, ident) for PSL(2, p), p an odd prime (elements are matrices up to sign)."""
    grid = np.array(list(itertools.product(range(p), repeat=4)), dtype=np.int64)
    det = (grid[:, 0] * grid[:, 3] - grid[:, 1] * grid[:, 2]) % p
    grid = grid[det == 1]

    def key(x):
        return ((x[:, 0] * p + x[:, 1]) * p + x[:, 2]) * p + x[:, 3]

    def negkey(x):
        return key((-x) % p)

    k = key(grid)
    kn = negkey(grid)
    reps = grid[k <= kn]  # canonical representative of each +-M pair
    n = len(reps)
    lookup = np.full(p ** 4, -1, dtype=np.int64)
    lookup[key(reps)] = np.arange(n)

    a1 = reps[:, 0][:, None]
    b1 = reps[:, 1][:, None]
    c1 = reps[:, 2][:, None]
    d1 = reps[:, 3][:, None]
    a2 = reps[:, 0][None, :]
    b2 = reps[:, 1][None, :]
    c2 = reps[:, 2][None, :]
    d2 = reps[:, 3][None, :]
    pa = (a1 * a2 + b1 * c2) % p
    pb = (a1 * b2 + b1 * d2) % p
    pc = (c1 * a2 + d1 * c2) % p
    pd = (c1 * b2 + d1 * d2) % p
    P = np.stack([pa.ravel(), pb.ravel(), pc.ravel(), pd.ravel()], axis=1)
    canon = np.minimum(key(P), negkey(P))
    mul = lookup[canon].reshape(n, n)
    ident = int(lookup[key(np.array([[1, 0, 0, 1]], dtype=np.int64))[0]])
    return n, mul, ident


def _cyclic(m):
    """Return (order, mul, ident) for Z_m."""
    ar = np.arange(m, dtype=np.int64)
    return m, (ar[:, None] + ar[None, :]) % m, 0


# ----------------------------------------------------------------------------
# Haar graphs over a group: A_g ~ B_{g s} for s in S.
# Vertex g (0..n-1) is A_g, vertex n + h is B_h.
# Left multiplication is an automorphism, so the diameter equals the larger of
# the eccentricities of A_e and B_e. Cost = number of vertices not reached
# within D steps from those two sources; cost 0 means diameter <= D.
# ----------------------------------------------------------------------------

def _make_nbr(n, mul, inv, S):
    Sa = np.array(S, dtype=np.int64)
    return np.vstack([n + mul[:, Sa], mul[:, inv[Sa]]])


def _cost(nbr, n, ident, D):
    N = 2 * n
    total = 0
    for src in (0, n + ident):
        vis = np.zeros(N, dtype=bool)
        vis[src] = True
        front = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = nbr[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += N - int(vis.sum())
    return total


def _search(n, mul, inv, ident, d, D, rng, deadline):
    """Hill climbing with annealing over the connection set S. Returns S with cost 0, or None."""
    S = rng.sample(range(n), d)
    cur = _cost(_make_nbr(n, mul, inv, S), n, ident, D)
    best_c = cur
    stall = 0
    temp = 1.5
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        new = rng.randrange(n)
        if new in S:
            continue
        S2 = S[:]
        S2[i] = new
        c2 = _cost(_make_nbr(n, mul, inv, S2), n, ident, D)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            S, cur = S2, c2
        if cur < best_c:
            best_c = cur
            stall = 0
        else:
            stall += 1
            if stall > 4000:  # restart from a random connection set
                S = rng.sample(range(n), d)
                cur = _cost(_make_nbr(n, mul, inv, S), n, ident, D)
                best_c = cur
                stall = 0
    return S


def _inverse_table(mul, ident):
    return np.argmax(mul == ident, axis=1)


# ----------------------------------------------------------------------------
# Exact construction for D = 3.
# ----------------------------------------------------------------------------

def _pg_exact(d):
    """Incidence graph of PG(2, d-1) when d-1 is a prime power, else None."""
    q = d - 1
    if q >= 2 and lib.is_prime_power(q):
        return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Main build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d}, diameter 2.
    fb_n, fb_e = lib.haar_graph(d, range(d))
    best_n, best_e = fb_n, fb_e

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    if not lib.is_valid(best_n, best_e, d, D):
        return 1, []

    if D >= 3:
        pg = _pg_exact(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3:
                return best_n, best_e

    if d < 2:
        return best_n, best_e

    # Group candidates: PSL(2,p) and cyclic groups, filtered by the Moore bound.
    mb = lib.moore_bound(d, D)
    cands = []
    for p in (5, 7, 11, 13, 17, 19):
        o = p * (p * p - 1) // 2
        if o <= 1600 and 2 * o > best_n and 2 * o <= mb and o >= d:
            cands.append(("psl", p, o))
    lo = best_n // 2 + 1
    for m in range(max(lo, d), lo + 3):
        if 2 * m > best_n and 2 * m <= mb and m >= d:
            cands.append(("cyc", m, m))
    cands.sort(key=lambda c: c[2])  # ascending: secure small improvements first

    for idx, (kind, param, order) in enumerate(cands):
        if 2 * order <= best_n:
            continue
        now = time.monotonic()
        remaining = deadline - now
        if remaining <= 0.5:
            break
        slot_end = now + remaining / (len(cands) - idx)
        try:
            if kind == "psl":
                n, mul, ident = _psl2(param)
            else:
                n, mul, ident = _cyclic(param)
            if n < d or 2 * n <= best_n:
                continue
            inv = _inverse_table(mul, ident)
            S = _search(n, mul, inv, ident, d, D, rng, slot_end)
            if S is not None:
                nbr = _make_nbr(n, mul, inv, S)
                edges = [(g, int(v)) for g in range(n) for v in nbr[g]]
                consider(2 * n, edges)
        except Exception:
            continue

    return best_n, best_e
