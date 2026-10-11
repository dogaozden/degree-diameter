import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# D = 3 and D = 4 structured starts: projective plane and generalized quadrangle.
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 7 for speed."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Semidirect-product groups and bi-Cayley / multi-base voltage lifts.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _groups(N):
    """Return semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


# ----------------------------------------------------------------------------
# NEW ROUTINE: vectorised multi-source reachability on a regular lift.
#
# Every vertex of a d-regular lift has exactly one neighbour per layer L, so the
# whole graph is described by an integer table nb of shape (V, d). Reachability
# from several sources is then a boolean array R of shape (sources, V), and one
# BFS level is the single fancy-indexing step R[:, nb].any(axis=2). The inverse
# permutation of each layer is stored too, so B-side rows are filled by slicing,
# with no per-vertex Python loop.
# ----------------------------------------------------------------------------

def _perm_pair(mul, G, s):
    """Right translation g -> g*s as an array, together with its inverse permutation."""
    pm = np.array([mul(g, s) for g in range(G)], dtype=np.int64)
    inv = np.empty(G, dtype=np.int64)
    inv[pm] = np.arange(G, dtype=np.int64)
    return pm, inv


def _nbr_table(k, G, darts, perms):
    """Neighbour table nb[v, L] for the lift; darts are ordered as dart t = L*k + i."""
    d = len(darts) // k
    nb = np.empty((2 * k * G, d), dtype=np.int64)
    for t, ((i, j, _s), (pm, inv)) in enumerate(zip(darts, perms)):
        L = t // k
        nb[i * G:(i + 1) * G, L] = (k + j) * G + pm
        nb[(k + j) * G:(k + j + 1) * G, L] = i * G + inv
    return nb


def _unreached_vec(nb, srcs, D):
    """Number of (source, vertex) pairs not within distance D, for all sources at once."""
    V = nb.shape[0]
    S = len(srcs)
    R = np.zeros((S, V), dtype=bool)
    R[np.arange(S), srcs] = True
    for _ in range(D):
        nxt = R | R[:, nb].any(axis=2)
        if np.array_equal(nxt, R):
            break
        R = nxt
    return S * V - int(np.count_nonzero(R))


def _eval(k, G, D, darts, perms):
    """Cost of a configuration (zero means valid). Duplicate darts give _BIG."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    nb = _nbr_table(k, G, darts, perms)
    srcs = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    return _unreached_vec(nb, srcs, D)


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), (pm, _inv) in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + int(pm[g])))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_perm_pair(mul, G, s) for _, _, s in darts]
    cost = _eval(k, G, D, darts, perms)

    T0 = max(1.0, 0.05 * cost) if cost < _BIG else 1.0
    T_end = 0.5
    decay = (T_end / T0) ** (1.0 / max(1, iters)) if T0 > T_end else 1.0
    T = T0

    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(T_end, T * decay)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_pair = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _perm_pair(mul, G, new_s)
            c2 = _eval(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_pair
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _eval(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

ANNEAL_ITERS = 8000   # annealing steps per attempt (cheap with the vectorised cost)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Structured starts.
    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: lifts with k base vertices per side over a semidirect group of
    # order G, giving 2kG vertices. Aim strictly above the current best.
    while best[0] < moore and time.monotonic() < deadline:
        n_best = best[0]
        k = rng.choice((1, 1, 2, 3))
        lo = n_best // (2 * k) + 1
        hi = moore // (2 * k)
        if lo > hi:
            if k == 1:
                break
            continue
        G = lo + rng.randrange(min(8, hi - lo + 1))
        groups = _groups(G)
        if not groups:
            continue
        m, k2, r = rng.choice(groups)
        order, mul, _ = lib.semidirect_group(m, k2, r)
        res = _anneal(d, D, k, order, mul, rng, deadline, ANNEAL_ITERS)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
