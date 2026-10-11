import itertools
import math
import random
import time

import numpy as np

import lib

ITERS = 1200          # annealing steps per (group, voltage plan) try
MAX_GROUPS = 40       # groups tried per attempt
KS = (1, 2, 3)        # number of A-orbits (and B-orbits) in the voltage lift


# ----------------------------------------------------------------------------
# Baseline families (fast, always valid when they pass lib.is_valid).
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
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Helper routine 1: vectorised group tables for Z_m x| Z_k (numpy, no Python loops).
# Element (a, b) is coded a*k + b, matching lib.semidirect_group.
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


def _group_tables(m, k, r, N):
    """Return (T, inv): T[x, g] = x*g and inv[g] = g^-1 as int64 numpy arrays of a group of order N."""
    x = np.arange(N, dtype=np.int64)
    a, b = x // k, x % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    T = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k + (b[:, None] + b[None, :]) % k
    gb = (-b) % k
    ga = (-pw[gb] * a) % m
    inv = ga * k + gb
    return T, inv


# ----------------------------------------------------------------------------
# Helper routine 2 (new): orbit-representative eccentricity via numpy BFS.
# A voltage lift of a bipartite base with K A-orbits and K B-orbits is
# invariant under left multiplication by the group, so the diameter is at most D
# iff every BFS from one representative per orbit (2K sources) reaches all
# 2KN vertices within D steps. Each BFS is D vectorised neighbour expansions.
# ----------------------------------------------------------------------------

def _plan(K, d, rng):
    """d random permutations of K orbits: each A-orbit and B-orbit gets exactly d darts.

    Dart e = t*K + i joins A-orbit i to B-orbit perm_t[i]; its slot is t on both sides.
    """
    plan = []
    for _ in range(d):
        perm = list(range(K))
        rng.shuffle(perm)
        for i in range(K):
            plan.append((i, perm[i]))
    return plan


def _init(plan, N, rng):
    """Random voltages, distinct within each (i, j) block so no parallel edges arise."""
    H = [0] * len(plan)
    by = {}
    for e, key in enumerate(plan):
        by.setdefault(key, []).append(e)
    for es in by.values():
        for e, v in zip(es, rng.sample(range(N), len(es))):
            H[e] = v
    return H


def _others(plan):
    by = {}
    for e, key in enumerate(plan):
        by.setdefault(key, []).append(e)
    return [[f for f in by[plan[e]] if f != e] for e in range(len(plan))]


def _energy(K, N, d, D, plan, T, inv, H):
    """Number of (source, vertex) pairs at distance > D over orbit representatives."""
    V = 2 * K * N
    KN = K * N
    nb = np.empty((V, d), dtype=np.int64)
    for e, (i, j) in enumerate(plan):
        t = e // K
        h = H[e]
        nb[i * N:(i + 1) * N, t] = KN + j * N + T[:, h]
        nb[KN + j * N:KN + (j + 1) * N, t] = i * N + T[:, int(inv[h])]
    sources = [i * N for i in range(K)] + [KN + j * N for j in range(K)]
    total = 0
    for s in sources:
        seen = np.zeros(V, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            mask = np.zeros(V, dtype=bool)
            mask[nb[front].ravel()] = True
            mask &= ~seen
            if not mask.any():
                break
            seen |= mask
            front = np.flatnonzero(mask)
        total += V - int(np.count_nonzero(seen))
    return total


def _anneal(K, N, d, D, plan, T, inv, others, H, rng, iters, deadline):
    """Simulated annealing over voltages to zero the number of far pairs."""
    cur = _energy(K, N, d, D, plan, T, inv, H)
    for it in range(iters):
        if cur == 0:
            return H
        if time.monotonic() > deadline:
            break
        e = rng.randrange(len(H))
        c = rng.randrange(N)
        if c == H[e] or any(H[f] == c for f in others[e]):
            continue
        H2 = H[:]
        H2[e] = c
        v = _energy(K, N, d, D, plan, T, inv, H2)
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            H, cur = H2, v
    return H if cur == 0 else None


def _attempt(K, N, d, D, rng, deadline):
    """Try groups of order N with K-orbit voltage lifts until one has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() >= deadline:
            return None
        T, inv = _group_tables(m, k, r, N)
        plan = _plan(K, d, rng)
        others = _others(plan)
        H = _init(plan, N, rng)
        H = _anneal(K, N, d, D, plan, T, inv, others, H, rng, ITERS, deadline)
        if H is not None:
            return plan, T, H
    return None


def _lift_edges(K, N, plan, T, H):
    """Return (n, edges) of the voltage lift: A-vertices 0..KN-1, B-vertices KN..2KN-1."""
    KN = K * N
    edges = []
    for e, (i, j) in enumerate(plan):
        col = T[:, H[e]].tolist()
        for x in range(N):
            edges.append((i * N + x, KN + j * N + col[x]))
    return 2 * KN, edges


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.8 * time_limit, time_limit - 5.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Record-matching case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)
    budget = {K: 0.8 for K in KS}
    nxt = {K: 1 for K in KS}

    # Round-robin over the number of orbits K. For each K we ratchet the group
    # order N upward from the smallest N that could beat the current best.
    while time.monotonic() < deadline:
        active = False
        for K in KS:
            if time.monotonic() >= deadline:
                break
            N = max(d, best_n // (2 * K) + 1, nxt[K])
            if 2 * K * N > moore:
                continue
            active = True
            end = min(deadline, time.monotonic() + budget[K])
            res = _attempt(K, N, d, D, rng, end)
            if res is None:
                budget[K] = min(budget[K] * 1.2, 20.0)
                continue
            plan, T, H = res
            n, edges = _lift_edges(K, N, plan, T, H)
            consider(n, edges)
            nxt[K] = N + 1
        if not active:
            break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
