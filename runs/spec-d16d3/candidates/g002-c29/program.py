import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Extension of PG(2, q) incidence graphs (diameter 3), q = largest prime power
# with q + 1 <= d, spare load s = d - q - 1 per vertex.
#
# Index j is both line j and point j (the incidence matrix M is symmetric).
# An extension A-vertex is a set T of indices (joined to lines T) that covers
# every point; a B-vertex is a set U of indices (joined to points U) that meets
# every line. Diameter 3 requires:
#   - every pair of A-sets shares an index, and every pair of B-sets shares one;
#   - every index is used by at most s sets in total (on both sides);
#   - every set has at most d indices.
# Pencils (all lines through a point P) give exactly the arc construction.
# Here a simulated annealing search tries to add one more set to a valid family.
# ----------------------------------------------------------------------------


def _best_q(d):
    qs = [x for x in range(2, d) if lib.is_prime_power(x)]
    return max(qs) if qs else None


def _greedy_centers(m, s, lines_thr, rng, trials, deadline):
    """Randomized greedy set of centers whose pencils keep every index load <= s."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = np.zeros(m, dtype=np.int64)
        chosen = []
        for P in order:
            js = lines_thr[P]
            if np.all(load[js] < s):
                chosen.append(P)
                load[js] += 1
        if len(chosen) > len(best):
            best = chosen
    return best


def _random_row(m, k, rng):
    r = np.zeros((1, m), dtype=np.int8)
    r[0, rng.sample(range(m), min(k, m))] = 1
    return r


def _sa(M, pts_on, s, cap, X, deadline, rng):
    """Anneal a family of index sets (rows of X) to zero cost. Returns X or None."""
    f, m = X.shape
    X = X.astype(np.int64)
    Mi = M.astype(np.int64)
    cov = X @ Mi.T                      # cov[a, p] = #indices of set a on point p
    load = X.sum(axis=0)                # load[j] = #sets containing index j
    sizes = X.sum(axis=1)
    inter = X @ X.T
    iu = np.triu_indices(f, 1)
    cost = (int(np.count_nonzero(cov == 0))
            + int(np.maximum(load - s, 0).sum())
            + int(np.maximum(sizes - cap, 0).sum())
            + int(np.count_nonzero(inter[iu] == 0)))

    T0, T1 = 1.0, 0.05
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T = T0
    it = 0
    while cost > 0:
        it += 1
        if it % 256 == 0:
            now = time.monotonic()
            if now >= deadline:
                break
            T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        a = rng.randrange(f)
        j = rng.randrange(m)
        sign = -1 if X[a, j] else 1
        idx = pts_on[j]
        c = cov[a, idx]
        if sign > 0:
            du = -int(np.count_nonzero(c == 0))
        else:
            du = int(np.count_nonzero(c == 1))
        lo = int(load[j])
        so = int(sizes[a])
        do = max(0, lo + sign - s) - max(0, lo - s)
        ds = max(0, so + sign - cap) - max(0, so - cap)
        others = np.nonzero(X[:, j])[0]
        others = others[others != a]
        if others.size:
            old = inter[a, others]
            new = old + sign
            dz = int(np.count_nonzero(new == 0)) - int(np.count_nonzero(old == 0))
        else:
            dz = 0
        delta = du + do + ds + dz
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            X[a, j] += sign
            cov[a, idx] += sign
            load[j] += sign
            sizes[a] += sign
            if others.size:
                inter[a, others] += sign
                inter[others, a] += sign
            cost += delta

    if cost == 0:
        return X.astype(np.int8)
    return None


def _graph(base, m, X):
    """Build the extended graph from the family X (rows = index sets)."""
    f = X.shape[0]
    n = 2 * m + 2 * f
    E = list(base)
    for x in range(f):
        for j in np.nonzero(X[x])[0]:
            E.append((2 * m + x, m + int(j)))          # A-vertex on lines
    for y in range(f):
        for p in np.nonzero(X[y])[0]:
            E.append((2 * m + f + y, int(p)))          # B-vertex on points
    return n, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.6 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    q = _best_q(d)
    if D == 2 or q is None:
        return lib.haar_graph(d, range(d))   # K_{d,d}, diameter 2

    # Baseline: PG(2, q) incidence graph, degree q+1 <= d, diameter 3.
    n0, base = lib.projective_plane_incidence(q)
    m = n0 // 2
    best = (n0, base)
    if not lib.is_valid(n0, base, d, D):
        best = lib.haar_graph(d, range(d))
    s = d - q - 1
    if s <= 0:
        return best

    M = np.zeros((m, m), dtype=np.int8)
    for u, v in base:
        M[u, v - m] = 1
    pts_on = [np.nonzero(M[:, j])[0] for j in range(m)]
    lines_thr = [np.nonzero(M[P])[0] for P in range(m)]

    centers = _greedy_centers(m, s, lines_thr, rng, 40, start + 0.2 * time_limit)
    if not centers:
        return best
    X = M[centers].copy()                    # warm start: pencils of an arc
    cap = d

    # Try to add one more set to the family; keep the largest valid graph.
    while time.monotonic() < deadline - 1.0:
        row = _random_row(m, q + 1, rng)
        Xn = np.vstack([X, row])
        remaining = deadline - time.monotonic()
        chunk_end = min(deadline, time.monotonic() + max(2.0, remaining / 3.0))
        Y = _sa(M, pts_on, s, cap, Xn, chunk_end, rng)
        if Y is None:
            continue
        n, E = _graph(base, m, Y)
        if n > best[0] and lib.is_valid(n, E, d, D):
            best = (n, E)
            X = Y

    return best
