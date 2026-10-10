import itertools
import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count for the lift search
ITERS = 6000                  # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side for lifts
GQ_Q_MAX = 8                  # largest q for which W(q) is built
RETRIES = 2                   # lift annealing attempts per candidate size
REPAIR_ITERS = 4000           # edge-swap annealing iterations per repair attempt
REPAIR_M_CAP = 400            # max vertices per side in the repair search
LIFT_TIME_FRAC = 0.4          # fraction of the budget given to lifts before repair


# ---------------------------------------------------------------- D = 3 : projective plane

def _pg_augmented(d, seed):
    """Incidence graph of PG(2,q) with q the largest prime power <= d-1, plus spare-degree edges."""
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


# ---------------------------------------------------------------- D = 4 : generalized quadrangle

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    for q in range(min(d - 1, GQ_Q_MAX), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ---------------------------------------------------------------- lifts (annealing)

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


def _cost(nbr, sources, D):
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


def _anneal(s, m, d, D, rng, deadline):
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(m) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * m for i in range(2 * s)]
    nbr = _neighbors(P, Pinv, V, s, m)
    cur = _cost(nbr, sources, D)
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
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            a, b = rng.sample(range(s), 2)
            _swap(P, Pinv, k, a, b)
            cand = _neighbors(P, Pinv, V, s, m)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, a, b)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, m, P, V, d):
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


def _try_size(s, m, d, D, rng, deadline):
    for _ in range(RETRIES):
        if time.monotonic() > deadline:
            break
        st = _anneal(s, m, d, D, rng, deadline)
        if st is not None:
            return st
    return None


def _search(s, d, D, rng, deadline, cap):
    best = None
    lo, hi = 0, None
    m = 1
    while time.monotonic() < deadline:
        if 2 * s * m > cap:
            hi = m
        else:
            st = _try_size(s, m, d, D, rng, deadline)
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


# ---------------------------------------------------------------- repair: degree-preserving edge swaps

def _bad_pairs_fast(m, d, E, D):
    """Number of unordered vertex pairs at distance > D in the bipartite graph given by edge list E.

    Vertices: A-side a in 0..m-1, B-side b mapped to m+b. Every vertex has degree exactly d.
    """
    n = 2 * m
    nbr = np.zeros((n, d), dtype=np.int64)
    ca = [0] * m
    cb = [0] * m
    for a, b in E:
        nbr[a, ca[a]] = m + b
        ca[a] += 1
        nbr[m + b, cb[b]] = a
        cb[b] += 1
    R = np.eye(n, dtype=bool)
    for _ in range(D):
        M = R.copy()
        for k in range(d):
            M |= R[:, nbr[:, k]]
        if np.array_equal(M, R):
            break
        R = M
    return (n * n - int(np.count_nonzero(R))) // 2


def _repair(m, d, D, rng, deadline, iters):
    """Anneal a d-regular bipartite graph on m+m vertices by double-edge swaps until diameter <= D.

    Returns the edge list E (pairs (a, b) with b in 0..m-1 for the B side), or None.
    """
    E = [[a, (a + k) % m] for a in range(m) for k in range(d)]
    S = set((a, b) for a, b in E)
    L = len(E)

    def check(i, j):
        a1, b1 = E[i]
        a2, b2 = E[j]
        if a1 == a2 or b1 == b2:
            return False
        return (a1, b2) not in S and (a2, b1) not in S

    def apply(i, j):
        a1, b1 = E[i]
        a2, b2 = E[j]
        S.discard((a1, b1))
        S.discard((a2, b2))
        S.add((a1, b2))
        S.add((a2, b1))
        E[i] = [a1, b2]
        E[j] = [a2, b1]

    # Randomise the start (degree preserved, simple graph preserved).
    for _ in range(4 * L):
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i != j and check(i, j):
            apply(i, j)

    cur = _bad_pairs_fast(m, d, E, D)
    it = 0
    while cur > 0 and it < iters and time.monotonic() < deadline:
        it += 1
        i = rng.randrange(L)
        j = rng.randrange(L)
        if i == j or not check(i, j):
            continue
        apply(i, j)
        c = _bad_pairs_fast(m, d, E, D)
        temp = 1.5 * (1.0 - it / iters) + 0.05
        if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
            cur = c
        else:
            apply(i, j)  # the reverse of a swap is the same swap on the new pair
    return E if cur == 0 else None


def _repair_search(d, D, lo, rng, deadline, cap_m):
    """Find the largest m (vertices per side) for which the repair annealing succeeds."""
    best = None
    hi = None
    step = 2
    m_try = max(lo + 2, d)
    while time.monotonic() < deadline and m_try <= cap_m:
        now = time.monotonic()
        att_deadline = min(deadline, now + max(1.0, (deadline - now) / 3.0))
        E = _repair(m_try, d, D, rng, att_deadline, REPAIR_ITERS)
        if E is not None:
            best = (m_try, E)
            lo = m_try
            if hi is None:
                nxt = min(lo + step, cap_m)
                if nxt <= lo:
                    break
                m_try = nxt
                step *= 2
            else:
                if hi - lo <= 1:
                    break
                m_try = (lo + hi) // 2
        else:
            hi = m_try
            if hi - lo <= 1:
                break
            m_try = max(d, (lo + hi) // 2)
            if m_try >= hi:
                break
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.75 * time_limit - 1.0)
    deadline = start + total
    lift_deadline = start + LIFT_TIME_FRAC * total

    # Trivial fallbacks, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if d < 1 or D < 1:
        return fallback if d >= 1 else (1, [])
    if D == 1:
        return (2, [(0, 1)]) if d >= 1 else (1, [])
    if d == 1:
        return (2, [(0, 1)])

    best = fallback

    def consider(c):
        nonlocal best
        if c is not None and c[0] > best[0] and lib.is_valid(c[0], c[1], d, D):
            best = c

    # D = 3: projective plane PG(2,q), q the largest prime power <= d-1, augmented with spare degree.
    if D == 3 and d >= 3:
        pg = _pg_augmented(d, seed)
        if pg is not None:
            consider(pg)
            if lib.is_prime_power(d - 1) and best is pg:
                return best

    # D >= 4: generalized quadrangle W(q), diameter 4 <= D.
    if D >= 4:
        consider(_best_gq(d))

    moore = lib._moore_bound(d, D)

    # Phase 1: voltage-lift annealing (structured search).
    rng = random.Random(seed)
    cap = min(N_CAP, moore)
    best_lift = None  # (n, s, m, P, V)
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= lift_deadline:
            break
        slice_end = now + (lift_deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            m, P, V = res
            n = 2 * s * m
            if best_lift is None or n > best_lift[0]:
                best_lift = (n, s, m, P, V)

    if best_lift is not None:
        n, e = _graph(best_lift[1], best_lift[2], best_lift[3], best_lift[4], d)
        consider((n, e))

    # Phase 2: unstructured repair search on a d-regular bipartite graph (edge swaps),
    # started from the best valid size found so far and pushed to larger sizes.
    if d >= 3 and best[0] < moore and time.monotonic() < deadline:
        rng2 = random.Random(seed * 7919 + 17)
        cap_m = min(moore // 2, REPAIR_M_CAP)
        if cap_m >= d:
            res = _repair_search(d, D, best[0] // 2, rng2, deadline, cap_m)
            if res is not None:
                m, E = res
                edges = [(a, m + b) for a, b in E]
                consider((2 * m, edges))

    return best
