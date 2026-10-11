import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New construction: bipartite d-regular graphs as d permutation layers between
# two sides of size m, optimised by degree-preserving 2-switches (simulated
# annealing on the number of vertex pairs at distance greater than D).
#
# Distances are computed with packed bitsets over numpy (one row per vertex),
# so a full evaluation costs a few milliseconds for n around 1100.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


def _base_reach(N):
    """Packed bitset matrix where row v has only bit v set."""
    W = (N + 63) // 64
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    vals = np.left_shift(np.ones(N, dtype=np.uint64), (v & 63).astype(np.uint64))
    base[v, v >> 6] = vals
    return base


def _reach_bits(nbr, D, base):
    """Vertices reachable within D steps, as packed bitsets."""
    reach = base
    for _ in range(D):
        new = reach.copy()
        for l in range(nbr.shape[0]):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _bad_stats(reach, N):
    """Return (total unreached ordered pairs, per-vertex count of unreached vertices)."""
    pc = _POP8[reach.view(np.uint8)]
    row = pc.sum(axis=1)
    return N * N - int(row.sum()), N - row


def _anneal(d, D, m, rng, deadline, T0=6.0, T1=0.5):
    """Search for d permutation layers on m+m vertices with diameter <= D. Returns sigma or None."""
    N = 2 * m
    a = np.arange(m, dtype=np.int64)

    # Start from distinct cyclic shifts: duplicate-free by construction.
    sig = np.empty((d, m), dtype=np.int64)
    for l, s in enumerate(rng.sample(range(m), d)):
        sig[l] = (a + s) % m

    C = np.zeros((m, m), dtype=np.int64)  # C[x, y] = number of layers joining x to y
    for l in range(d):
        C[a, sig[l]] += 1

    nbr = np.empty((d, N), dtype=np.int64)
    nbr[:, :m] = sig + m
    inv = np.empty((d, m), dtype=np.int64)
    inv[np.arange(d)[:, None], sig] = a[None, :]
    nbr[:, m:] = inv

    def swap(l, a1, a2):
        """Exchange the images of A-vertices a1, a2 in layer l. Applying it twice restores the state."""
        b1 = int(sig[l, a1])
        b2 = int(sig[l, a2])
        C[a1, b1] -= 1
        C[a2, b2] -= 1
        C[a1, b2] += 1
        C[a2, b1] += 1
        sig[l, a1] = b2
        sig[l, a2] = b1
        nbr[l, a1] = m + b2
        nbr[l, a2] = m + b1
        nbr[l, m + b2] = a1
        nbr[l, m + b1] = a2

    def valid_swap(l, a1, a2):
        b1 = int(sig[l, a1])
        b2 = int(sig[l, a2])
        return C[a1, b2] == 0 and C[a2, b1] == 0

    # Randomise with duplicate-free switches (accepted unconditionally).
    base = _base_reach(N)
    for _ in range(4 * m * d):
        l = rng.randrange(d)
        a1 = rng.randrange(m)
        a2 = rng.randrange(m)
        if a1 == a2 or not valid_swap(l, a1, a2):
            continue
        swap(l, a1, a2)

    reach = _reach_bits(nbr, D, base)
    cost, rowmiss = _bad_stats(reach, N)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)

    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = min(1.0, (now - t0) / span)
        T = T0 * (T1 / T0) ** frac

        l = rng.randrange(d)
        bad = np.flatnonzero(rowmiss)
        if bad.size and rng.random() < 0.5:
            v = int(bad[rng.randrange(bad.size)])
            a1 = v if v < m else int(nbr[l, v])
        else:
            a1 = rng.randrange(m)
        a2 = rng.randrange(m)
        if a1 == a2 or not valid_swap(l, a1, a2):
            continue

        swap(l, a1, a2)
        r2 = _reach_bits(nbr, D, base)
        c2, rm2 = _bad_stats(r2, N)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            cost, rowmiss, reach = c2, rm2, r2
        else:
            swap(l, a1, a2)

    return sig


def _edges_from_sig(sig, m):
    d = sig.shape[0]
    return [(a, m + int(sig[l, a])) for l in range(d) for a in range(m)]


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < deadline - 10:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline - 2:
        half = lib.moore_bound(d, D) // 2
        lo = best_n // 2          # sizes at or below this are already covered
        m = max(lo + 1, int(0.36 * half), d)
        hi = None
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 1.5 or m >= half or m <= lo:
                break
            if hi is not None and hi - lo <= 2:
                break
            attempt_end = min(deadline, time.monotonic() + max(1.0, 0.5 * remaining))
            sig = _anneal(d, D, m, rng, attempt_end)
            if sig is not None:
                consider(2 * m, _edges_from_sig(sig, m))
                lo = m
                if hi is None:
                    m = m + max(2, m // 40)
                else:
                    m = (lo + hi) // 2
            else:
                hi = m
                m = (lo + hi) // 2

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
