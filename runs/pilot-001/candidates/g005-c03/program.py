import math
import random
import time

import numpy as np

import lib

N_CAP = 6000                  # hard cap on vertex count for the lift search
ITERS = 3000                  # annealing iterations per lift attempt
S_LIST = (1, 2, 3, 4, 5, 6)   # number of base vertices per side
DENSE_CAP = 1400              # vertex cap for the direct bipartite annealing search

POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)


# ---------------------------------------------------------------- group lifts (parent method)

def _group_shapes(M):
    """Return group shapes (a, b) with a*b = M to try: the cyclic one and the most balanced one."""
    shapes = [(1, M)]
    best = None
    for a in range(2, math.isqrt(M) + 1):
        if M % a == 0:
            best = a
    if best is not None:
        shapes.append((best, M // best))
    return shapes


def _nbr(P, Pinv, V, s, a, b):
    """Neighbour table (n x d) of the Z_a x Z_b lift of a d-regular bipartite base on s+s vertices."""
    M = a * b
    d = P.shape[0]
    G = np.arange(M, dtype=np.int64)
    GX, GY = G // b, G % b
    nbr = np.empty((2 * s * M, d), dtype=np.int64)
    for k in range(d):
        for i in range(s):
            j = int(P[k, i])
            v = int(V[k, i])
            vx, vy = v // b, v % b
            tgt = ((GX + vx) % a) * b + (GY + vy) % b
            nbr[i * M:(i + 1) * M, k] = s * M + j * M + tgt
        for j in range(s):
            i = int(Pinv[k, j])
            v = int(V[k, i])
            vx, vy = v // b, v % b
            tgt = ((GX - vx) % a) * b + (GY - vy) % b
            nbr[(s + j) * M:(s + j + 1) * M, k] = i * M + tgt
    return nbr


def _cost(nbr, sources, D):
    """Number of (source, vertex) pairs NOT within distance D. Zero iff the lift is valid."""
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


def _anneal(s, a, b, d, D, rng, deadline):
    """Simulated annealing over permutations and group voltages. Returns (P, V) with zero cost, or None."""
    M = a * b
    P = np.array([rng.sample(range(s), s) for _ in range(d)], dtype=np.int64)
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    V = np.array([[rng.randrange(M) for _ in range(s)] for _ in range(d)], dtype=np.int64)
    sources = [i * M for i in range(2 * s)]
    nbr = _nbr(P, Pinv, V, s, a, b)
    cur = _cost(nbr, sources, D)
    for it in range(ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = 2.0 * (1.0 - it / ITERS) + 0.05
        if s == 1 or rng.random() < 0.7:
            k, i = rng.randrange(d), rng.randrange(s)
            old = int(V[k, i])
            new_v = rng.randrange(M)
            if new_v == old:
                continue
            V[k, i] = new_v
            cand = _nbr(P, Pinv, V, s, a, b)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                V[k, i] = old
        else:
            k = rng.randrange(d)
            x, y = rng.sample(range(s), 2)
            _swap(P, Pinv, k, x, y)
            cand = _nbr(P, Pinv, V, s, a, b)
            c = _cost(cand, sources, D)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur, nbr = c, cand
            else:
                _swap(P, Pinv, k, x, y)
    if cur == 0:
        return P.copy(), V.copy()
    return None


def _graph(s, a, b, P, V, d):
    """Materialise the group lift as (n, edges), deduplicated."""
    M = a * b
    Pinv = np.zeros_like(P)
    for k in range(d):
        for i in range(s):
            Pinv[k, P[k, i]] = i
    nbr = _nbr(P, Pinv, V, s, a, b)
    edges = set()
    for x in range(s * M):
        for y in nbr[x].tolist():
            edges.add((x, y))
    return 2 * s * M, sorted(edges)


def _search(s, d, D, rng, deadline, cap):
    """For fixed s, find the largest group order M (doubling then bisection) with a passing lift."""
    best = None
    lo, hi = 0, None
    M = 1
    while time.monotonic() < deadline:
        if 2 * s * M > cap:
            hi = M
        else:
            res = None
            for a, b in _group_shapes(M):
                if time.monotonic() >= deadline:
                    break
                st = _anneal(s, a, b, d, D, rng, deadline)
                if st is not None:
                    res = (a, b, st[0], st[1])
                    break
            if res is not None:
                lo = M
                best = res
            else:
                hi = M
        if hi is None:
            M = 2 * lo
        else:
            if hi - lo <= 1:
                break
            M = (lo + hi) // 2
    return best


# ---------------------------------------------------------------- D = 3 base (parent method)

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


def _parent_build(d, D, seed, deadline):
    """Parent pipeline: projective-plane base for D=3, otherwise group-lift annealing."""
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])
    else:
        fallback = (1, [])

    pg = None
    if D == 3 and d >= 3:
        cand = _pg_augmented(d, seed)
        if cand is not None and lib.is_valid(cand[0], cand[1], d, D):
            pg = cand
            if lib.is_prime_power(d - 1):
                return pg

    if D < 2 or d < 1:
        return pg if pg is not None else fallback

    rng = random.Random(seed)
    cap = min(N_CAP, lib._moore_bound(d, D))
    best = None
    for idx, s in enumerate(S_LIST):
        now = time.monotonic()
        if now >= deadline:
            break
        slice_end = now + (deadline - now) / (len(S_LIST) - idx)
        res = _search(s, d, D, rng, slice_end, cap)
        if res is not None:
            a, b, P, V = res
            n = 2 * s * a * b
            if best is None or n > best[0]:
                best = (n, s, a, b, P, V)

    lift = None
    if best is not None:
        n, e = _graph(best[1], best[2], best[3], best[4], best[5], d)
        if lib.is_valid(n, e, d, D):
            lift = (n, e)

    options = [c for c in (pg, lift, fallback) if c is not None]
    return max(options, key=lambda c: c[0])


# ---------------------------------------------------------------- new: direct bipartite annealing

def _dense_cost(P, m, d, D):
    """Ordered pairs not within distance D in the bipartite graph given by d perfect matchings P (d x m).

    Reachability is kept as packed uint64 bitsets, one row per vertex.
    """
    n = 2 * m
    W = (n + 63) // 64
    nbr = np.empty((n, d), dtype=np.int64)
    nbr[:m] = m + P.T
    Pinv = np.argsort(P, axis=1)
    nbr[m:] = Pinv.T
    idx = np.arange(n, dtype=np.int64)
    reach = np.zeros((n, W), dtype=np.uint64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        nr = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(nr, reach):
            break
        reach = nr
    cnt = int(POP8[reach.view(np.uint8)].sum())
    return n * n - cnt


def _dense_anneal(m, d, D, rng, deadline):
    """Anneal d disjoint perfect matchings between two m-sets until diameter <= D. Returns P or None."""
    P = np.empty((d, m), dtype=np.int64)
    for k in range(d):
        ok = False
        for _ in range(100):
            perm = np.array(rng.sample(range(m), m), dtype=np.int64)
            if all(np.all(P[j] != perm) for j in range(k)):
                P[k] = perm
                ok = True
                break
        if not ok:
            return None
    cur = _dense_cost(P, m, d, D)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur > 0:
        now = time.monotonic()
        if now >= deadline:
            return None
        frac = (now - t0) / span
        T = 2.5 * (1.0 - frac) + 0.1
        k = rng.randrange(d)
        x, y = rng.sample(range(m), 2)
        conflict = False
        for j in range(d):
            if j != k and (P[j, x] == P[k, y] or P[j, y] == P[k, x]):
                conflict = True
                break
        if conflict:
            continue
        P[k, x], P[k, y] = P[k, y], P[k, x]
        c = _dense_cost(P, m, d, D)
        if c <= cur or rng.random() < math.exp(-(c - cur) / T):
            cur = c
        else:
            P[k, x], P[k, y] = P[k, y], P[k, x]
    return P


def _dense_build(d, D, seed, deadline, n_hint):
    """Bisection over the side size m, running direct annealing at each size. Returns valid (n, edges) or None."""
    rng = random.Random(seed + 1)
    cap = min(DENSE_CAP, lib._moore_bound(d, D))
    lo = None
    hi = None
    best = None
    m = max(d + 1, n_hint // 2)
    while time.monotonic() < deadline - 0.2:
        if 2 * m > cap:
            hi = m if hi is None else min(hi, m)
        else:
            now = time.monotonic()
            budget = max(0.3, (deadline - now) * 0.4)
            P = _dense_anneal(m, d, D, rng, min(deadline, now + budget))
            if P is not None:
                lo = m if lo is None else max(lo, m)
                best = (m, P)
            else:
                hi = m if hi is None else min(hi, m)
        if lo is not None and hi is not None:
            if hi - lo <= 1:
                break
            m = (lo + hi) // 2
        elif hi is None:
            m = int(m * 1.15) + 1
        else:
            if m <= d + 1:
                break
            m = max(d + 1, int(m * 0.8))
    if best is None:
        return None
    m, P = best
    Pl = P.tolist()
    edges = [(i, m + Pl[k][i]) for k in range(d) for i in range(m)]
    n = 2 * m
    if lib.is_valid(n, edges, d, D):
        return (n, edges)
    return None


# ---------------------------------------------------------------- entry point

def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, 0.8 * time_limit - 1.0)
    end = start + total

    # Safe fallback, always valid where stated.
    if D >= 2 and d >= 1:
        fallback = lib.haar_graph(d, range(d))      # K_{d,d}: diameter 2
    elif D >= 1 and d >= 1:
        fallback = (2, [(0, 1)])                     # K_2
    else:
        fallback = (1, [])

    if D < 1 or d < 1:
        return fallback

    # Weakest cases get the new direct construction; the rest keep the parent pipeline.
    weak = (D >= 4 and d >= 3) or (D == 3 and d >= 8)

    parent = None
    try:
        parent_deadline = start + (0.5 * total if weak else total)
        parent = _parent_build(d, D, seed, parent_deadline)
        if parent is not None and not lib.is_valid(parent[0], parent[1], d, D):
            parent = None
    except Exception:
        parent = None

    options = [fallback]
    if parent is not None:
        options.append(parent)

    if weak:
        try:
            dense = _dense_build(d, D, seed, end, parent[0] if parent is not None else 0)
        except Exception:
            dense = None
        if dense is not None:
            options.append(dense)

    return max(options, key=lambda c: c[0])
