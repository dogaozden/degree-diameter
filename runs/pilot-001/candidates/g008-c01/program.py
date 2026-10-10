import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                 # hard cap on vertex count
ITERS_HAAR = 4000            # annealing steps per Haar attempt
ITERS = 3000                 # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)  # base-vertex counts for the lift fallback


# ---------------------------------------------------------------- Haar / bi-Cayley search
# Graph: A-vertices i in Z_m, B-vertices m+j in Z_m, with A-i ~ B-(i+s) for s in S, |S| = d.
# Z_m acts by translation, so distances from A_0 and B_0 determine all pairwise distances.
# This is a single-orbit construction, different from the multi-orbit voltage lifts below.

def _haar_nbr(m, S):
    Sv = np.array(S, dtype=np.int64)
    a = np.arange(m, dtype=np.int64)[:, None]
    nbr = np.empty((2 * m, len(S)), dtype=np.int64)
    nbr[:m] = m + (a + Sv[None, :]) % m
    nbr[m:] = (a - Sv[None, :]) % m
    return nbr


def _haar_cost(nbr, m, D):
    """Unreached (source, vertex) pairs from A_0 and B_0 within distance D. Zero iff valid."""
    n = 2 * m
    R = np.zeros((2, n), dtype=bool)
    R[0, 0] = True
    R[1, m] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return 2 * n - int(np.count_nonzero(R))


def _anneal_haar(m, d, D, rng, deadline):
    if m < d:
        return None
    S = rng.sample(range(m), d)
    cur = _haar_cost(_haar_nbr(m, S), m, D)
    for it in range(ITERS_HAAR):
        if cur == 0 or time.monotonic() > deadline:
            break
        pos = rng.randrange(d)
        new = rng.randrange(m)
        if new in S:
            continue
        old = S[pos]
        S[pos] = new
        c = _haar_cost(_haar_nbr(m, S), m, D)
        temp = 2.0 * (1.0 - it / ITERS_HAAR) + 0.05
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            S[pos] = old
    return list(S) if cur == 0 else None


def _search_haar(d, D, rng, deadline, cap_m):
    """Largest m (doubling then bisection) with a valid Haar graph found by annealing."""
    lo = d                       # K_{d,d} (m = d, S = all residues) is always valid for D >= 2
    best = (d, list(range(d)))
    hi = cap_m + 1               # sentinel: "no infeasible m found yet"
    while time.monotonic() < deadline:
        if hi == cap_m + 1:
            if lo >= cap_m:
                break
            m = min(max(2 * lo, d), cap_m)
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
        now = time.monotonic()
        slice_end = min(deadline, now + max(0.3, (deadline - now) / 2))
        S = _anneal_haar(m, d, D, rng, slice_end)
        if S is not None:
            lo = m
            best = (m, S)
        else:
            hi = m
    return best


def _haar_graph(m, S):
    return 2 * m, [(i, m + (i + s) % m) for i in range(m) for s in S]


# ---------------------------------------------------------------- D = 3 projective plane

def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q), q the largest prime power <= d-1, plus spare-degree edges."""
    q = d - 1
    while q >= 2 and not lib.is_prime_power(q):
        q -= 1
    if q < 2:
        return None
    n, edges = lib.projective_plane_incidence(q)
    m = n // 2
    deg = [0] * n
    adj = [set() for _ in range(n)]
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        adj[u].add(v)
        adj[v].add(u)
    rng = random.Random(seed)
    new_edges = list(edges)
    for _ in range(3):
        pts = [p for p in range(m) if deg[p] < d]
        rng.shuffle(pts)
        for p in pts:
            if deg[p] >= d:
                continue
            cands = [l for l in range(m, n) if deg[l] < d and l not in adj[p]]
            if not cands:
                continue
            l = rng.choice(cands)
            adj[p].add(l)
            adj[l].add(p)
            deg[p] += 1
            deg[l] += 1
            new_edges.append((p, l))
    return n, new_edges


# ---------------------------------------------------------------- voltage lift fallback

def _neighbors(P, Pinv, V, s, m):
    d = P.shape[0]
    g = np.arange(m, dtype=np.int64)
    nbr = np.empty((2 * s * m, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            nbr[i * m:(i + 1) * m, k] = s * m + j * m + (g + int(V[k, i])) % m
        for j in range(s):
            i = int(Pinv[k, j])
            nbr[(s + j) * m:(s + j + 1) * m, k] = i * m + (g - int(V[k, i])) % m
    return nbr


def _lift_cost(nbr, sources, D):
    n = nbr.shape[0]
    S = len(sources)
    R = np.zeros((S, n), dtype=bool)
    R[np.arange(S), sources] = True
    for _ in range(D):
        M = R.copy()
        for k in range(nbr.shape[1]):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return int(S * n - np.count_nonzero(R))


def _swap(P, Pinv, k, a, b):
    P[k, a], P[k, b] = P[k, b], P[k, a]
    Pinv[k, P[k, a]] = a
    Pinv[k, P[k, b]] = b


def _anneal_lift(s, m, d, D, rng, deadline):
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _lift_cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(m)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _neighbors(P, Pinv, V, s, m)
            c = _lift_cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _lift_cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _lift_graph(s, m, P, V, d):
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _neighbors(P, Pinv, V, s, m)
    edges = set()
    for x in range(s * m):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * m, sorted(edges)


def _search_lift(s, d, D, rng, deadline, cap):
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _anneal_lift(s, m, d, D, rng, deadline)
            if st is not None:
                lo = m
                best = (m, st[0], st[1])
            else:
                hi = m
        if hi is None:
            m = 2 * lo
        else:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- main

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, 0.6 * time_limit - 1.0)

    # Always-valid fallbacks.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}, diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])
    else:
        fallback = (1, [])

    cands = [fallback]

    # D = 3: projective-plane construction.
    if D == 3 and d >= 3:
        pg = _pg_augmented(d, seed)
        if pg is not None and lib.is_valid(pg[0], pg[1], d, D):
            if lib.is_prime_power(d - 1):
                return pg
            cands.append(pg)

    if D < 2 or d < 2:
        return max(cands, key=lambda c: c[0])

    rng = random.Random(seed)
    moore = lib._moore_bound(d, D)
    cap = min(N_CAP, moore)

    # Bold change: single-orbit bi-Cayley (Haar) search gets the first 60% of the budget.
    split = start + (deadline - start) * 0.6
    cap_m = cap // 2
    if cap_m >= d:
        res = _search_haar(d, D, rng, split, cap_m)
        if res is not None:
            m, S = res
            n, e = _haar_graph(m, S)
            if lib.is_valid(n, e, d, D):
                cands.append((n, e))

    # Remaining budget: voltage-lift search as a secondary candidate.
    best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search_lift(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best is None or n > best[0]:
                best = (n, s, m, P, V)

    if best is not None:
        n, e = _lift_graph(best[1], best[2], best[3], best[4], d)
        if lib.is_valid(n, e, d, D):
            cands.append((n, e))

    return max(cands, key=lambda c: c[0])
