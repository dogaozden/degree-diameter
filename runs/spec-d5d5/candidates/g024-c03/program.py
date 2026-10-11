import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Structured baselines (valid for D = 3 and D = 4 respectively).
# ----------------------------------------------------------------------------

def _pg_baseline(d):
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


def _gq_baseline(d):
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables built with numpy.
# ----------------------------------------------------------------------------

_TAB = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m * k = N, giving Z_m x|_r Z_k."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(m, k, r):
    """(order N, T, invs) with T[x, y] = x*y and invs[g] = g^-1 for Z_m x|_r Z_k.

    Element (a, b) is coded as a*k + b, matching lib.semidirect_group.
    """
    key = (m, k, r)
    hit = _TAB.get(key)
    if hit is not None:
        return hit
    N = m * k
    x = np.arange(N, dtype=np.int64)
    a = x // k
    b = x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    invs = np.argmax(T == 0, axis=1).astype(np.int64)
    if len(_TAB) >= 12:
        _TAB.clear()
    _TAB[key] = (N, T, invs)
    return _TAB[key]


# ----------------------------------------------------------------------------
# Family A: Bi-Cayley lifts (one base vertex per side), numpy BFS cost.
# A_x ~ B_{x*g} for g in S. Left translation is an automorphism, so checking
# eccentricities of A_0 and B_0 suffices.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _bc_cost(N, T, invs, S, D):
    Sa = np.asarray(S, dtype=np.int64)
    Si = invs[Sa]
    TS = T[:, Sa]
    TSi = T[:, Si]
    total = 0
    for side in (0, 1):
        FA = np.zeros(N, dtype=bool)
        FB = np.zeros(N, dtype=bool)
        if side == 0:
            FA[0] = True
        else:
            FB[0] = True
        RA = FA.copy()
        RB = FB.copy()
        for _ in range(D):
            if not (FA.any() or FB.any()):
                break
            nB = np.zeros(N, dtype=bool)
            nA = np.zeros(N, dtype=bool)
            xs = np.flatnonzero(FA)
            if xs.size:
                nB[TS[xs].ravel()] = True
            ys = np.flatnonzero(FB)
            if ys.size:
                nA[TSi[ys].ravel()] = True
            nB &= ~RB
            nA &= ~RA
            RB |= nB
            RA |= nA
            FA, FB = nA, nB
        total += 2 * N - int(RA.sum()) - int(RB.sum())
    return total


def _anneal_bc(N, T, invs, d, D, rng, iters, deadline):
    S = [0] + rng.sample(range(1, N), d - 1)
    cur = _bc_cost(N, T, invs, S, D)
    best_S, best_v = list(S), cur
    T0 = 2.0 + 0.05 * cur
    for step in range(iters):
        if best_v == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.2
        i = rng.randrange(1, d)
        c = rng.randrange(1, N)
        if c in S:
            continue
        S2 = list(S)
        S2[i] = c
        v = _bc_cost(N, T, invs, S2, D)
        delta = v - cur
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            S, cur = S2, v
            if cur < best_v:
                best_S, best_v = list(S), cur
    return best_S if best_v == 0 else None


# ----------------------------------------------------------------------------
# Family B: multi-base voltage lifts with k base vertices per side.
# Vertex A_{i,x} = i*G + x, B_{j,y} = (k+j)*G + y.
# Dart (i, j, s) gives A_{i,x} ~ B_{j, x*s}. Each layer is a perfect matching
# between A-bases and B-bases, so the lift is d-regular.
# ----------------------------------------------------------------------------

def _mb_cost(k, G, T, invs, darts, D):
    if len(set(darts)) < len(darts):
        return _BIG
    Ps = [T[:, s] for (_, _, s) in darts]
    Qs = [T[:, invs[s]] for (_, _, s) in darts]
    total = 0
    for side in (0, 1):
        for base in range(k):
            FA = np.zeros((k, G), dtype=bool)
            FB = np.zeros((k, G), dtype=bool)
            if side == 0:
                FA[base, 0] = True
            else:
                FB[base, 0] = True
            RA = FA.copy()
            RB = FB.copy()
            for _ in range(D):
                nA = np.zeros((k, G), dtype=bool)
                nB = np.zeros((k, G), dtype=bool)
                for t, (i, j, _s) in enumerate(darts):
                    if FA[i].any():
                        nB[j, Ps[t]] |= FA[i]
                    if FB[j].any():
                        nA[i, Qs[t]] |= FB[j]
                nA &= ~RA
                nB &= ~RB
                RA |= nA
                RB |= nB
                FA, FB = nA, nB
                if not (FA.any() or FB.any()):
                    break
            total += 2 * k * G - int(RA.sum()) - int(RB.sum())
    return total


def _anneal_mb(k, G, T, invs, d, D, rng, iters, deadline):
    darts = []
    for L in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append((i, p[i], rng.randrange(G)))
    cost = _mb_cost(k, G, T, invs, darts, D)
    T0 = 5.0 if cost >= _BIG else 2.0 + 0.05 * cost
    for step in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = T0 * (1.0 - step / iters) + 0.3
        cand = list(darts)
        if k == 1 or rng.random() < 0.7:
            idx = rng.randrange(len(darts))
            i, j, s = darts[idx]
            ns = rng.randrange(G)
            if ns == s:
                continue
            cand[idx] = (i, j, ns)
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            ta, tb = darts[ia], darts[ib]
            cand[ia] = (ta[0], tb[1], ta[2])
            cand[ib] = (tb[0], ta[1], tb[2])
        c2 = _mb_cost(k, G, T, invs, cand, D)
        delta = c2 - cost
        if delta <= 0 or rng.random() < math.exp(-delta / temp):
            darts, cost = cand, c2
    if cost != 0:
        return None
    E = set()
    for i, j, s in darts:
        col = T[:, s].tolist()
        for x in range(G):
            E.add((i * G + x, (k + j) * G + col[x]))
    return 2 * k * G, sorted(E)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

ITERS_BC = 1500
ITERS_MB = 900


def _complete_bipartite(d):
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = _complete_bipartite(d)
    if D == 2:
        return fallback

    best = fallback
    moore = lib._moore_bound(d, D)

    def consider(n, e):
        nonlocal best
        try:
            if n > best[0] and lib.is_valid(n, e, d, D):
                best = (n, e)
        except Exception:
            pass

    # Structured baselines.
    try:
        if D == 3:
            pg = _pg_baseline(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4:
            gq = _gq_baseline(d)
            if gq is not None:
                consider(gq[0], gq[1])
    except Exception:
        pass

    # Main search: lifts of order above the current best.
    while best[0] < moore and d >= 2 and time.monotonic() < deadline:
        try:
            n_best = best[0]
            k = rng.choice((1, 1, 2, 2, 3))
            lo = n_best // (2 * k) + 1
            if 2 * k * lo > moore:
                continue
            G = lo + rng.randrange(max(2, lo // 8))
            if G < d + 1:
                continue
            groups = _groups(G)
            if not groups:
                continue
            m, k2, r = rng.choice(groups)
            N, T, invs = _tables(m, k2, r)
            if k == 1:
                S = _anneal_bc(N, T, invs, d, D, rng, ITERS_BC, deadline)
                if S is not None:
                    edges = [(x, N + int(T[x, g])) for x in range(N) for g in S]
                    consider(2 * N, edges)
            else:
                res = _anneal_mb(k, N, T, invs, d, D, rng, ITERS_MB, deadline)
                if res is not None:
                    consider(res[0], res[1])
        except Exception:
            continue

    try:
        if not lib.is_valid(best[0], best[1], d, D):
            best = fallback
    except Exception:
        best = fallback
    return best
