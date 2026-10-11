import math
import random
import time

import numpy as np

import lib

ITERS = 4000               # annealing steps per attempt
TIME_FRAC = 0.75           # fraction of time_limit used in total
TIME_MARGIN = 2.0          # seconds kept in reserve
GENERIC_M_CAP = 300        # cap on group order for D != 3 (keeps tables cheap)
GROUPS_PER_M = 4           # max number of groups tried per order


# ---------------------------------------------------------------- safe fallbacks

def _pg_base(d):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1 (diameter 3)."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    return lib.projective_plane_incidence(q)


def _araujo(d):
    """Araujo-Pardo and Lopez record graph for d = q+2 with q a prime power (diameter 3)."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    try:
        return lib.araujo_lopez_graph(q)
    except Exception:
        return None


# ---------------------------------------------------------------- bi-Cayley graphs
#
# A group G of order m and a connection set S (|S| = d) give the bipartite graph
#   A-x ~ B-(x*g)  for all x in G, g in S.
# It is d-regular, bipartite, and vertex-transitive on each side. Its diameter is at
# most D iff the balls of radius D around A-e and B-e cover everything, which is
# checked directly by the cost function below.

def _groups_for(m, rng):
    """Descriptors of groups of order m: cyclic, plus a few semidirect products Z_a x| Z_k."""
    out = [("Z",)]
    for k in range(2, m):
        if m % k:
            continue
        a = m // k
        if a < 2:
            continue
        rs = [r for r in range(2, a) if math.gcd(r, a) == 1 and pow(r, k, a) == 1 % a]
        rng.shuffle(rs)
        for r in rs[:2]:
            out.append(("S", a, k, r))
    rng.shuffle(out)
    return out[:GROUPS_PER_M]


def _table(desc, m):
    """Multiplication table (m x m) and inverse array of the group described by desc."""
    if desc[0] == "Z":
        ar = np.arange(m, dtype=np.int64)
        mt = (ar[:, None] + ar[None, :]) % m
        inv = (-ar) % m
        return mt, inv
    _, a, k, r = desc
    _, mulf, invf = lib.semidirect_group(a, k, r)
    mt = np.array([[mulf(x, y) for y in range(m)] for x in range(m)], dtype=np.int64)
    inv = np.array([invf(x) for x in range(m)], dtype=np.int64)
    return mt, inv


def _cost(mt, inv, S, m, D):
    """Number of (source, vertex) pairs not within distance D, sources A-e and B-e.

    Zero iff the bi-Cayley graph has diameter <= D (left multiplication is an automorphism).
    """
    invS = inv[S]
    k = S.shape[0]
    nbr = np.empty((2 * m, k), dtype=np.int64)
    nbr[:m] = m + mt[:, S]     # A-x -> B-(x g)
    nbr[m:] = mt[:, invS]      # B-y -> A-(y g^-1)
    R = np.zeros((2, 2 * m), dtype=bool)
    R[0, 0] = True
    R[1, m] = True
    for _ in range(D):
        M = R.copy()
        for j in range(k):
            M |= R[:, nbr[:, j]]
        if np.array_equal(M, R):
            break
        R = M
    return 4 * m - int(np.count_nonzero(R))


def _anneal(mt, inv, m, k, D, rng, iters, deadline):
    """Anneal a connection set S of size k in the group. Returns sorted S with cost 0, or None."""
    S = rng.sample(range(m), k)
    inS = set(S)
    cur = _cost(mt, inv, np.array(S, dtype=np.int64), m, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        i = rng.randrange(k)
        new = rng.randrange(m)
        if new in inS:
            continue
        old = S[i]
        S[i] = new
        c = _cost(mt, inv, np.array(S, dtype=np.int64), m, D)
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
            inS.discard(old)
            inS.add(new)
        else:
            S[i] = old
    return sorted(S) if cur == 0 else None


def _search(d, D, m_lo, m_hi, rng, deadline):
    """Try orders m = m_lo..m_hi in ascending order, each with an equal share of the time.

    Returns the (n, edges) of the largest valid bi-Cayley graph found, or None.
    """
    best = None
    ms = list(range(m_lo, m_hi + 1))
    tables = {}
    for idx, m in enumerate(ms):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(ms) - idx)
        groups = _groups_for(m, rng)
        while time.monotonic() < slice_end:
            desc = groups[rng.randrange(len(groups))]
            key = (m, desc)
            if key not in tables:
                try:
                    tables[key] = _table(desc, m)
                except ValueError:
                    continue
            mt, inv = tables[key]
            S = _anneal(mt, inv, m, d, D, rng, ITERS, slice_end)
            if S is None:
                continue
            n = 2 * m
            edges = [(x, m + int(mt[x, g])) for x in range(m) for g in S]
            if lib.is_valid(n, edges, d, D):
                best = (n, edges)   # ascending m, so later hits are larger
                break
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, TIME_FRAC * time_limit - TIME_MARGIN)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallbacks, all validated. K_{d,d} has diameter 2 and is always valid for D >= 2.
    kn, ke = lib.haar_graph(d, range(d))
    cands = [(kn, ke)]
    if D >= 3:
        pg = _pg_base(d)
        if pg is not None:
            cands.append(pg)
        if D == 3:
            ar = _araujo(d)
            if ar is not None:
                cands.append(ar)

    best = None
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if lib.is_valid(n, e, d, D):
            best = (n, e)
            break
    if best is None:
        return kn, ke

    # Bold path: bi-Cayley graphs over non-cyclic groups, searched for orders above the fallback.
    if D >= 3 and time.monotonic() < deadline:
        if D == 3:
            m_hi = d * d - d + 1          # |S S^-1| <= d^2 - d + 1 is necessary
        else:
            m_hi = min(lib._moore_bound(d, D) // 2, GENERIC_M_CAP)
        m_lo = max(d, best[0] // 2 + 1)   # only orders that beat the fallback matter
        if m_lo <= m_hi:
            found = _search(d, D, m_lo, m_hi, rng, deadline)
            if found is not None and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                best = found

    return best

