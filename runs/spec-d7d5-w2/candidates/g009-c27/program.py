import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or classical baselines (kept as safe fallbacks).
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
# NEW CONSTRUCTION: Haar graphs over finite groups with coverage annealing.
#
# For a group G (here Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a+r^b c, b+e))
# and a set S of d distinct generators, the Haar graph H(G, S) has
#   A-vertices g (0..G-1) and B-vertices G+h (h in G),
#   with A_g adjacent to B_{g*s} for every s in S.
# This is d-regular and bipartite, and left multiplication is an automorphism
# acting transitively on each side. So diameter <= D holds iff the A-representative
# e and the B-representative e reach every vertex within D steps.
#
# Each candidate S is scored by the number of unreached (vertex, representative)
# pairs, computed with 2-bit reachability masks in numpy. Simulated annealing
# swaps single generators. Groups of increasing order are sampled, and the order
# grows whenever a zero-cost S is found. The result is checked with lib.is_valid.
# This differs from the parent's block-voltage search: it has a single base
# block per side, a one-number-per-vertex cost, and it climbs the group order.
# ----------------------------------------------------------------------------

def _tables(m, k, r):
    """Return (G, Ts, Full) for Z_m x|_r Z_k.

    Ts[s, g] = g*s. Full[s] is the neighbour array of generator s over all 2G vertices:
    A-vertex g -> G + g*s, B-vertex G+h -> the g with g*s = h.
    """
    G = m * k
    x = np.arange(G, dtype=np.int64)
    a = x // k
    b = x % k
    powers = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    Full = np.concatenate([G + Ts, Invs], axis=1)
    return G, Ts, Full


def _cost(G, Full, S, D):
    """Number of unreached (vertex, representative) pairs for the Haar graph with generators S."""
    reach = np.zeros(2 * G, dtype=np.int64)
    reach[0] = 1       # A-representative (bit 0)
    reach[G] = 2       # B-representative (bit 1)
    for _ in range(D):
        new = reach.copy()
        for s in S:
            new |= reach[Full[s]]
        if np.array_equal(new, reach):
            break
        reach = new
    pc = (reach & 1) + ((reach >> 1) & 1)
    return 4 * G - int(pc.sum())


def _anneal(G, Full, d, D, rng, deadline, iters):
    """Simulated annealing over d-element generator sets. Returns the list S or None."""
    S = rng.sample(range(G), d)
    Sset = set(S)
    c = _cost(G, Full, S, D)
    for t in range(iters):
        if c == 0:
            break
        if (t & 127) == 0 and time.monotonic() > deadline:
            return None
        temp = max(0.2, 1.5 * (1.0 - t / iters))
        l = rng.randrange(d)
        x = rng.randrange(G)
        if x in Sset:
            continue
        old = S[l]
        S[l] = x
        c2 = _cost(G, Full, S, D)
        if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
            c = c2
            Sset.discard(old)
            Sset.add(x)
        else:
            S[l] = old
    return list(S) if c == 0 else None


def _sample_group(G, rng):
    """Return (m, k, r) with m*k = G and r^k = 1 mod m, gcd(r, m) = 1, or None."""
    ks = [k for k in range(1, min(G, 40) + 1) if G % k == 0]
    rng.shuffle(ks)
    for k in ks[:10]:
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            return m, k, rng.choice(rs)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Haar-graph search over groups of increasing order.
    if D >= 3 and d >= 2:
        moore = lib.moore_bound(d, D)
        lo = max(d, best_n // 2)
        while time.monotonic() < deadline:
            span = lo // 12 + 1
            G = lo + 1 + rng.randrange(span)
            if 2 * G > moore:
                break
            grp = _sample_group(G, rng)
            if grp is None:
                continue
            m, k, r = grp
            Gt, Ts, Full = _tables(m, k, r)
            S = _anneal(Gt, Full, d, D, rng, deadline, 2500)
            if S is not None:
                edges = [(g, Gt + int(Ts[s, g])) for s in S for g in range(Gt)]
                if consider(2 * Gt, edges):
                    lo = Gt

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
