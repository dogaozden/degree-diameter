import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Tunables.
# ----------------------------------------------------------------------------

MAX_GROUPS = 6        # semidirect groups tried per (k, G) attempt
ANNEAL_ITERS = 1500   # annealing steps per (group, base-size) attempt
BIG = 10 ** 9


# ----------------------------------------------------------------------------
# Structured baselines for D = 3 and D = 4 (projective planes, quadrangles).
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
                    v = tuple(F.add(F.mul(a, x[t]), F.mul(b, y[t])) for t in range(4))
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-base voltage lifts over semidirect products Z_m x|_r Z_k.
#
# Base: k "A" vertices and k "B" vertices, each lifted to a copy of the group G
# (order G). Layer L is a perfect matching between A-base and B-base vertices,
# giving d darts (i, j, s) in total; dart (i, j, s) joins A_{i,g} to B_{j, g*s}.
# Left multiplication by h is an automorphism, so it suffices to check that
# each of the 2k base vertices (at identity) reaches all 2kG vertices in D steps.
#
# k = 1 is a bi-Cayley graph with connection set S of size d.
# k >= 2 is a genuinely larger family (more freedom for the same order).
#
# The reachability check is vectorized over all 2k sources at once with
# boolean arrays, so each evaluation costs a handful of numpy calls per step.
# ----------------------------------------------------------------------------

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


def _semidirect_table(m, k, r):
    """T[x, g] = x*g in Z_m x|_r Z_k, with element (a, b) coded as a*k + b (identity 0)."""
    G = m * k
    x = np.arange(G, dtype=np.int64)[:, None]
    y = np.arange(G, dtype=np.int64)[None, :]
    a, b = x // k, x % k
    c, e = y // k, y % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    return ((a + pw[b] * c) % m) * k + (b + e) % k


def _inverses(T):
    """inv[g] = h with g*h = identity (identity is code 0)."""
    G = T.shape[0]
    rows, cols = np.nonzero(T == 0)
    inv = np.zeros(G, dtype=np.int64)
    inv[rows] = cols
    return inv


def _cost(k, G, D, darts, colR, invs):
    """Number of (source, vertex) pairs not reached within distance D. Zero means valid."""
    arr = np.asarray(darts, dtype=np.int64)
    I, J, S = arr[:, 0], arr[:, 1], arr[:, 2]
    keys = (I * k + J) * G + S
    if np.unique(keys).size < keys.size:
        return BIG  # parallel edges would result

    tgt = colR[S]          # tgt[t, g]  = g * s_t   (A -> B direction)
    tinv = colR[invs[S]]   # tinv[t, g] = g * s_t^-1 (B -> A direction)

    R = 2 * k
    FA = np.zeros((R, k, G), dtype=bool)
    FB = np.zeros((R, k, G), dtype=bool)
    for r in range(k):
        FA[r, r, 0] = True          # source r is A-base r at identity
        FB[k + r, r, 0] = True      # source k+r is B-base r at identity
    visA = FA.copy()
    visB = FB.copy()

    for _ in range(D):
        # Expand A-frontier to B-vertices.
        ra, ta, ga = np.nonzero(FA[:, I, :])
        NB = np.zeros((R, k, G), dtype=bool)
        NB[ra, J[ta], tgt[ta, ga]] = True
        NB &= ~visB
        # Expand B-frontier to A-vertices.
        rb, tb, gb = np.nonzero(FB[:, J, :])
        NA = np.zeros((R, k, G), dtype=bool)
        NA[rb, I[tb], tinv[tb, gb]] = True
        NA &= ~visA
        visA |= NA
        visB |= NB
        FA, FB = NA, NB
        if not (FA.any() or FB.any()):
            break

    covered = int(visA.sum()) + int(visB.sum())
    return R * 2 * k * G - covered


def _anneal(k, G, d, D, colR, invs, rng, iters, deadline):
    """Anneal voltages and per-layer B-assignments; return darts with zero cost, else None."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    cost = _cost(k, G, D, darts, colR, invs)

    for it in range(iters):
        if cost == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        temp = 0.2 + 2.0 * (1.0 - it / iters)

        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, colR, invs)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[idx][2] = old
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, colR, invs)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    return darts if cost == 0 else None


def _try_order(k, G, d, D, rng, deadline):
    """Try several semidirect groups of order G with k base vertices per side; return (n, edges) or None."""
    groups = _groups(G)
    rng.shuffle(groups)
    for m, kk, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            break
        T = _semidirect_table(m, kk, r)
        colR = np.ascontiguousarray(T.T)   # colR[s, g] = g * s
        invs = _inverses(T)
        darts = _anneal(k, G, d, D, colR, invs, rng, ANNEAL_ITERS, deadline)
        if darts is not None:
            Tl = T.tolist()
            E = []
            for i, j, s in darts:
                for g in range(G):
                    E.append((i * G + g, (k + j) * G + Tl[g][s]))
            return 2 * k * G, E
    return None


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 3.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for any D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Main search: lifts with k in {1, 2, 3} base vertices per side, aiming
    # strictly above the current best order.
    if d >= 2:
        nxt = {1: 0, 2: 0, 3: 0}
        dead = set()
        while best[0] < moore and time.monotonic() < deadline:
            feas = [k for k in (1, 2, 3) if k not in dead]
            if not feas:
                break
            k = rng.choice(feas)
            G = max(nxt[k], best[0] // (2 * k) + 1)
            if 2 * k * G > moore:
                dead.add(k)
                continue
            nxt[k] = G + 1
            res = _try_order(k, G, d, D, rng, deadline)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
