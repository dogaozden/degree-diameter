"""Two-class voltage lifts over non-abelian groups for d=10, D=5 (numpy + lib only).

Construction (new for this island): a bipartite base graph with two A-classes and two B-classes.
Blocks S00, S01, S10, S11 (sizes k, 10-k, 10-k, k) hold group elements. The lift on group G of
order N has 4N vertices: (g, A_i) ~ (s*g, B_j) for s in S_ij. Every row and column of the block
pattern sums to 10, so the graph is bipartite and 10-regular. Right multiplication by h is an
automorphism, so the diameter equals the maximum eccentricity over the four fibre representatives
(e, A_0), (e, A_1), (e, B_0), (e, B_1). Cost = total vertices unreached within distance 5 from
those four sources, so cost 0 is exactly diameter <= 5.

Order 4N with N >= 1001 beats the record 4000. A smaller order (N in 896..899) is tried first as
a secure fallback. The parent Haar graph (3582 vertices) is the last resort. Every returned graph
is checked with lib.is_valid.
"""
import math
import time

import numpy as np

import lib

TARGET = (10, 5)
PARENT_S = [0, 1754, 312, 1155, 1465, 922, 1459, 1712, 704, 1314]
SIDE_K = (4, 5, 6)


# ------------------------------------------------------------------ groups

def _finish(MT):
    MT = np.ascontiguousarray(MT, dtype=np.int32)
    inv = np.argmax(MT == 0, axis=1).astype(np.int32)
    return MT, inv


def group_meta(a, b, lam):
    """Z_a x|_lam Z_b, order a*b, element (x, j) coded as x*b + j."""
    if a < 1 or b < 1 or pow(lam, b, a) != 1 % a:
        raise ValueError("bad metacyclic parameters")
    pw = np.array([pow(lam, j, a) for j in range(b)], dtype=np.int64)
    N = a * b
    g = np.arange(N, dtype=np.int64)
    x, j = g // b, g % b
    MT = np.empty((N, N), dtype=np.int32)
    for lo in range(0, N, 256):
        hi = min(N, lo + 256)
        MT[lo:hi] = ((x[lo:hi, None] + pw[j[lo:hi], None] * x[None, :]) % a) * b \
            + (j[lo:hi, None] + j[None, :]) % b
    return _finish(MT)


def _specs(lo, hi, cap):
    """Group parameters (a, b, lam) with orders lo..hi; non-abelian first, then abelian."""
    nonab, ab = [], []
    for N in range(lo, hi + 1):
        for b in range(1, N + 1):
            if N % b:
                continue
            a = N // b
            if a < 2:
                continue
            if b == 1:
                ab.append((a, 1, 1))
                continue
            lams = [l for l in range(2, a) if math.gcd(l, a) == 1 and pow(l, b, a) == 1]
            for l in lams[:2]:
                nonab.append((a, b, l))
            ab.append((a, b, 1))
    return (nonab + ab)[:cap]


# ------------------------------------------------------------ lift and cost

def _random_blocks(m, k, rng):
    sizes = [k, 10 - k, 10 - k, k]
    return [rng.choice(m, s, replace=False).astype(np.int64) for s in sizes]


def _nbr(MT, inv, blocks, m):
    """Neighbour table (4m, 10). A-fibre i uses offset i*m, B-fibre j uses offset (2+j)*m."""
    S00, S01, S10, S11 = blocks
    Sij = [[S00, S01], [S10, S11]]
    nbr = np.empty((4 * m, 10), dtype=np.int64)
    offA = (0, m)
    offB = (2 * m, 3 * m)
    for i in range(2):
        cols = [MT[Sij[i][j]].T.astype(np.int64) + offB[j] for j in range(2)]
        nbr[offA[i]:offA[i] + m] = np.concatenate(cols, axis=1)
    for j in range(2):
        cols = [MT[inv[Sij[i][j]]].T.astype(np.int64) + offA[i] for i in range(2)]
        nbr[offB[j]:offB[j] + m] = np.concatenate(cols, axis=1)
    return nbr


def _unreached(nbr, src, D, n):
    seen = np.zeros(n, dtype=bool)
    seen[src] = True
    front = np.array([src], dtype=np.int64)
    for _ in range(D):
        nb = nbr[front].ravel()
        nb = nb[~seen[nb]]
        if nb.size == 0:
            break
        nb = np.unique(nb)
        seen[nb] = True
        front = nb
    return n - int(seen.sum())


def _cost(nbr, m, D):
    n = 4 * m
    return sum(_unreached(nbr, s, D, n) for s in (0, m, 2 * m, 3 * m))


def _anneal(MT, inv, m, k, deadline, rng, D):
    """Single-slot Metropolis search over the four blocks. Returns blocks with cost 0, or None."""
    blocks = _random_blocks(m, k, rng)
    cur = _cost(_nbr(MT, inv, blocks, m), m, D)
    since = 0
    while cur > 0 and time.monotonic() < deadline:
        b = int(rng.integers(4))
        blk = blocks[b]
        t = int(rng.integers(blk.size))
        x = int(rng.integers(m))
        if np.any(blk == x):
            continue
        nb = blk.copy()
        nb[t] = x
        trial = list(blocks)
        trial[b] = nb
        c = _cost(_nbr(MT, inv, trial, m), m, D)
        delta = c - cur
        T = 0.5 + 0.02 * cur
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            blocks, cur = trial, c
            since = 0
        else:
            since += 1
        if since > 3000:
            blocks = _random_blocks(m, k, rng)
            cur = _cost(_nbr(MT, inv, blocks, m), m, D)
            since = 0
    return blocks if cur == 0 else None


def _edges(nbr, m):
    edges = [(u, int(v)) for u in range(2 * m) for v in nbr[u]]
    return 4 * m, edges


def _search(specs, deadline, slice_len, rng, d, D):
    """Round-robin over group specs with time slices; returns the first checked valid graph."""
    while time.monotonic() < deadline:
        for a, b, lam in specs:
            now = time.monotonic()
            if now >= deadline:
                break
            try:
                MT, inv = group_meta(a, b, lam)
                m = a * b
                k = int(rng.choice(SIDE_K))
                end = min(deadline, now + slice_len)
                blocks = _anneal(MT, inv, m, k, end, rng, D)
                if blocks is None:
                    continue
                n, edges = _edges(_nbr(MT, inv, blocks, m), m)
                if lib.is_valid(n, edges, d, D):
                    return n, edges
            except Exception:
                continue
    return None


# ---------------------------------------------------------------- fallbacks

def _parent_haar(d, D):
    try:
        MT, _ = group_meta(199, 9, 180)
        N = MT.shape[0]
        g = np.arange(N)
        edges = [(int(a), int(N + b)) for s in PARENT_S for a, b in zip(g, MT[s])]
        if lib.is_valid(2 * N, edges, d, D):
            return 2 * N, edges
    except Exception:
        pass
    return None


def _small(d, D):
    try:
        if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and d - 1 <= 8:
            n, e = lib.projective_plane_incidence(d - 1)
        else:
            n, e = lib.haar_graph(d, range(d))
        if lib.is_valid(n, e, d, D):
            return n, e
    except Exception:
        pass
    if d >= 1 and D >= 1:
        return 2, [(0, 1)]
    return 1, []


# ---------------------------------------------------------------- entry

def _target(d, D, seed, time_limit):
    t0 = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    rng = np.random.default_rng(seed)
    best = None
    # Secure fallback: order 4N with N in 896..899 gives at least 3584 vertices.
    res = _search(_specs(896, 899, 6), t0 + 0.12 * total, 2.0, rng, d, D)
    if res is not None:
        best = res
    # Main attempt: order 4N with N in 1001..1004 beats the record 4000.
    res = _search(_specs(1001, 1004, 12), t0 + 0.92 * total, 5.0, rng, d, D)
    if res is not None:
        best = res
    if best is None:
        best = _parent_haar(d, D)
    return best


def build(d, D, seed, time_limit):
    if (d, D) == TARGET:
        try:
            res = _target(d, D, seed, time_limit)
        except Exception:
            res = None
        if res is not None:
            return res
    return _small(d, D)
