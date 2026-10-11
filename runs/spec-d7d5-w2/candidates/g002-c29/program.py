import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions for D = 3 and D = 4 (kept from the parent program).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph of degree d (q = d - 2 a prime power >= 3); diameter 3."""
    q = d - 2
    if q < 3 or not lib.is_prime_power(q):
        return None
    return lib.araujo_lopez_graph(q)


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
# New construction for D >= 5 (and as a fallback for D = 3, 4):
# simulated annealing directly over bipartite d-regular graphs.
#
# The graph has parts A = {0..s-1} and B = {s..2s-1}. Layer l is a permutation P[l]
# that joins A-vertex i to B-vertex s + P[l][i]. Every layer is a bijection, so the
# graph is d-regular and bipartite by construction. The only defect is duplicate edges,
# which are penalised.
#
# Moves swap two targets inside one layer, which keeps every layer a permutation.
# Cost = (ordered unreached vertex pairs at distance > D) + PEN * (duplicate edges).
# Reachability uses packed uint64 bitsets in numpy.
#
# A ladder over s grows the order on success and bisects between the last success
# and the last failure. Every result is verified with lib.is_valid.
# ----------------------------------------------------------------------------

_PEN = 2
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _unreached(nbr, n, D):
    """Number of ordered vertex pairs at distance > D (0 iff diameter <= D)."""
    W = (n + 63) // 64
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx // 64] = np.left_shift(np.uint64(1), (idx % 64).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=0)
        if np.array_equal(new, reach):
            break
        reach = new
    pc = int(_POP8[reach.view(np.uint8)].sum())
    return n * n - pc


def _set_layer(nbr, P, l, s):
    """Write layer l of the bipartite graph into the neighbour matrix."""
    nbr[l, :s] = s + P[l]
    nbr[l, s + P[l]] = np.arange(s, dtype=np.int64)


def _dups(P):
    """Number of duplicate (A, B) pairs across layers."""
    S = np.sort(P, axis=0)
    return int(np.count_nonzero(S[1:] == S[:-1]))


def _anneal(d, D, s, rng, g, deadline):
    """Anneal a d-layer permutation system on s + s vertices. Returns P or None."""
    n = 2 * s
    P = np.stack([g.permutation(s) for _ in range(d)]).astype(np.int64)
    nbr = np.empty((d, n), dtype=np.int64)
    for l in range(d):
        _set_layer(nbr, P, l, s)
    cost = _unreached(nbr, n, D) + _PEN * _dups(P)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        temp = 3.0 * (0.1 ** frac)
        l = rng.randrange(d)
        i1 = rng.randrange(s)
        i2 = rng.randrange(s)
        if i1 == i2:
            continue
        row = P[l]
        row[i1], row[i2] = row[i2], row[i1]
        _set_layer(nbr, P, l, s)
        c2 = _unreached(nbr, n, D) + _PEN * _dups(P)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            row[i1], row[i2] = row[i2], row[i1]
            _set_layer(nbr, P, l, s)
    return P


def _edges(P, s):
    """Edge list of the bipartite graph given by the layer permutations."""
    return [(i, s + int(P[l, i])) for l in range(P.shape[0]) for i in range(s)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)
    g_seed = abs(int(seed)) % (2 ** 32)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        try:
            if n > best_n and lib.is_valid(n, e, d, D):
                best = (n, e)
                best_n = n
        except Exception:
            pass

    # Exact constructions: return immediately when they are optimal.
    if D >= 3:
        try:
            pg = _best_pg(d)
        except Exception:
            pg = None
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

        if D == 3:
            try:
                aj = _araujo(d)
            except Exception:
                aj = None
            if aj is not None:
                consider(aj[0], aj[1])
                return best

    if D >= 4 and time.monotonic() < deadline:
        try:
            gq = _best_gq(d)
        except Exception:
            gq = None
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: annealing ladder over the part size s.
    # Invariant: lo is a size known to succeed (or the trivial K_{d,d}); hi is the
    # smallest size that failed so far, or None.
    if d >= 2 and D >= 3:
        lo, hi = d, None
        g_master = np.random.default_rng(g_seed)
        while True:
            now = time.monotonic()
            remaining = deadline - now
            if remaining < 0.2:
                break
            chunk = min(remaining, max(1.0, 0.2 * budget))
            if hi is None:
                s = lo + max(1, lo // 50)
            elif hi - lo > 1:
                s = (lo + hi) // 2
            else:
                s = hi
            sub = np.random.default_rng(int(g_master.integers(1 << 31)))
            try:
                P = _anneal(d, D, s, rng, sub, min(deadline, now + chunk))
            except Exception:
                P = None
            if P is not None:
                consider(2 * s, _edges(P, s))
                lo = s
                if hi is not None and hi <= lo:
                    hi = None
            else:
                hi = s if hi is None else min(hi, s)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
