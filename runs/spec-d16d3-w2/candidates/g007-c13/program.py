import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Construction A (new, bold): cyclic Haar graph from a difference cover.
#
# Haar graph H(Z_m, S): a_i ~ b_j iff j - i in S, with |S| = d. It is
# d-regular and bipartite on 2m vertices. If S - S covers all of Z_m, then
# every same-side pair is at distance <= 2, and every cross pair is at
# distance <= 3 (because S - S + S contains S - S + s0 = Z_m). So diameter 3
# holds. Since |S - S| <= d(d-1) + 1, we get m <= d(d-1) + 1, i.e. order
# <= 2(d(d-1)+1), which for d = 16 is 482, the stated ceiling.
#
# We search for a difference cover with simulated annealing and increase m
# step by step, carrying the previous cover forward as the starting point.
# ----------------------------------------------------------------------------

def _bump(cnt, m, others, v, sign):
    """Add (sign=+1) or remove (sign=-1) the differences between v and each element of others.
    Returns the change in the number of uncovered nonzero residues."""
    dz = 0
    for t in others:
        for x in ((v - t) % m, (t - v) % m):
            if sign > 0:
                if cnt[x] == 0:
                    dz -= 1
                cnt[x] += 1
            else:
                cnt[x] -= 1
                if cnt[x] == 0:
                    dz += 1
    return dz


def _cover_try(m, k, rng, deadline, init, iters):
    """Search for a k-subset S of Z_m (containing 0) whose difference set covers Z_m.
    Returns S as a list, or None on failure or timeout."""
    S = [0]
    inS = {0}
    if init:
        base = init[0]
        for s in init:
            r = (s - base) % m
            if r not in inS and len(S) < k:
                S.append(r)
                inS.add(r)
    while len(S) < k:
        x = rng.randrange(m)
        if x not in inS:
            S.append(x)
            inS.add(x)

    cnt = [0] * m
    for a in range(k):
        for b in range(k):
            if a != b:
                cnt[(S[a] - S[b]) % m] += 1
    zeros = sum(1 for x in range(1, m) if cnt[x] == 0)

    T = 0.5
    for it in range(iters):
        if zeros == 0:
            return S
        if (it & 511) == 0 and time.monotonic() > deadline:
            return None
        i = rng.randrange(1, k)
        old = S[i]
        x = rng.randrange(m)
        if x in inS:
            continue
        others = [S[j] for j in range(k) if j != i]
        dz1 = _bump(cnt, m, others, old, -1)
        dz2 = _bump(cnt, m, others, x, 1)
        delta = dz1 + dz2
        if delta <= 0 or rng.random() < math.exp(-delta / T):
            S[i] = x
            inS.discard(old)
            inS.add(x)
            zeros += delta
        else:
            _bump(cnt, m, others, x, -1)
            _bump(cnt, m, others, old, 1)
    return S if zeros == 0 else None


def _cyclic_search(k, deadline, rng):
    """Ascend m from k+1, keeping a difference cover at each step. Returns (m, S) or None."""
    best = None
    S = None
    m = k + 1
    maxm = k * (k - 1) + 1
    while m <= maxm and time.monotonic() < deadline:
        res = _cover_try(m, k, rng, deadline, S, 150000)
        if res is None:
            res = _cover_try(m, k, rng, deadline, None, 150000)
        if res is None:
            break
        S = res
        best = (m, list(res))
        m += 1
    return best


# ----------------------------------------------------------------------------
# Construction B (parent's best family, kept as a fallback): PG(2,q) plus a
# conic-based arc extension, degree d = q + 1 + s with s = 2 for q = 13, d = 16.
# ----------------------------------------------------------------------------

def _pg_conic(d):
    """Return (n, edges) for the best odd-q conic extension of PG(2,q), or None."""
    best = None
    for q in range(d - 3, 2, -1):
        if q % 2 == 0 or not lib.is_prime_power(q):
            continue
        s = d - q - 1
        if s < 2:
            continue
        m2, edges = lib.projective_plane_incidence(q)
        m = m2 // 2
        pts = lib.projective_points(q)
        index = {p: i for i, p in enumerate(pts)}
        F = lib.GF(q)
        S = [index[(1, t, F.mul(t, t))] for t in range(q)] + [index[(0, 0, 1)]]
        k = len(S)
        pl = [[] for _ in range(m)]
        lp = [[] for _ in range(m)]
        for u, v in edges:
            pl[u].append(v - m)
            lp[v - m].append(u)
        E = list(edges)
        for t, P in enumerate(S):
            a = 2 * m + t
            for L in pl[P]:
                E.append((a, m + L))
        for t, j in enumerate(S):
            b = 2 * m + k + t
            for Q in lp[j]:
                E.append((Q, b))
        n = 2 * m + 2 * k
        if lib.is_valid(n, E, d, 3):
            if best is None or n > best[0]:
                best = (n, E)
            break
    return best


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_E = lib.haar_graph(d, range(d))

    def consider(n, E):
        nonlocal best_n, best_E
        if n > best_n and lib.is_valid(n, E, d, D):
            best_n, best_E = n, [tuple(e) for e in E]

    if D == 3:
        pg = _pg_conic(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 3 and time.monotonic() < deadline:
        rng = random.Random(seed * 1000003 + d * 31 + D)
        res = _cyclic_search(d, deadline, rng)
        if res is not None:
            m, S = res
            if len(set(s % m for s in S)) == d:
                n, E = lib.haar_graph(m, S)
                consider(n, E)

    if not lib.is_valid(best_n, best_E, d, D):
        best_n, best_E = lib.haar_graph(d, range(d))
    return best_n, list(best_E)
