import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q): incidence graph, diameter 4, degree q+1.
# Used as a safe fallback for D >= 4.
# ----------------------------------------------------------------------------

def _gq_w(q):
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


def _saturate_bip(n, edges, d, P, rng):
    """Greedily add edges between left side [0,P) and right side [P,n) while degrees allow."""
    edges = list(edges)
    deg = [0] * n
    existing = set()
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
        existing.add((min(u, v), max(u, v)))
    pairs = [(a, b) for a in range(P) if deg[a] < d
             for b in range(P, n) if deg[b] < d and (a, b) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


# ----------------------------------------------------------------------------
# Bi-Cayley search (new construction).
#
# Let G be a finite group of order N with a d-subset S (identity allowed).
# Vertices a_x and b_x (x in G); edge a_x -- b_{x*s} for s in S.
# This is bipartite and d-regular on 2N vertices. Left multiplication by G
# is an automorphism, so each side is one orbit: diameter <= D is equivalent
# to both a_e and b_e having eccentricity <= D. Verification is two BFS.
# Search: hill-climb over S minimizing the number of vertices unreached within
# distance D from a_e and b_e.
# Groups: cyclic Z_N and semidirect products Z_m x| Z_k of order N.
# ----------------------------------------------------------------------------

def _groups(N, rng):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        if k == 1:
            out.append((N, 1, 1))
            continue
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    rng.shuffle(out)
    return out


def _cost(N, D, M, I, S):
    """Total number of (source, vertex) pairs unreached within D from a_e and from b_e."""
    Sinv = [I[s] for s in S]
    twoN = 2 * N
    total = 0
    for src in (0, N):
        seen = bytearray(twoN)
        seen[src] = 1
        frontier = [src]
        cnt = 1
        for _ in range(D):
            nxt = []
            for v in frontier:
                if v < N:
                    row = M[v]
                    for s in S:
                        w = N + row[s]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
                else:
                    row = M[v - N]
                    for si in Sinv:
                        w = row[si]
                        if not seen[w]:
                            seen[w] = 1
                            nxt.append(w)
            if not nxt:
                break
            cnt += len(nxt)
            frontier = nxt
        total += twoN - cnt
    return total


def _try_config(N, d, D, M, I, deadline, rng):
    """Hill-climb a d-subset S of G with cost 0; return S or None at the deadline."""
    S = rng.sample(range(N), d)
    cur = _cost(N, D, M, I, S)
    best_seen = cur
    stall = 0
    while cur > 0:
        if time.monotonic() > deadline:
            return None
        i = rng.randrange(d)
        t = rng.randrange(N)
        if t in S:
            continue
        old = S[i]
        S[i] = t
        c = _cost(N, D, M, I, S)
        if c <= cur or rng.random() < 0.01:
            cur = c
        else:
            S[i] = old
        if cur < best_seen:
            best_seen = cur
            stall = 0
        else:
            stall += 1
        if stall > 400:
            S = rng.sample(range(N), d)
            cur = _cost(N, D, M, I, S)
            best_seen = cur
            stall = 0
    return S


def _attempt(N, d, D, end, rng):
    """Try to find a bi-Cayley graph on 2N vertices; return (n, edges) or None."""
    if N < d:
        return None
    for cfg in _groups(N, rng):
        now = time.monotonic()
        if now >= end:
            break
        m, k, r = cfg
        order, mul, inv = lib.semidirect_group(m, k, r)
        Mt = [[mul(x, s) for s in range(order)] for x in range(order)]
        It = [inv(s) for s in range(order)]
        slice_end = min(end, now + 2.5)
        S = _try_config(order, d, D, Mt, It, slice_end, rng)
        if S is not None:
            edges = [(x, order + Mt[x][s]) for x in range(order) for s in S]
            if lib.is_valid(2 * order, edges, d, D):
                return (2 * order, edges)
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    M = lib._moore_bound(d, D)

    # Safe fallback: K_{d,d}, diameter 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []

    def consider(res):
        nonlocal best
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = (res[0], list(res[1]))

    if best[0] >= M:
        return best

    # D = 3 with d-1 a prime power: projective plane incidence meets the Moore bound.
    if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        consider(lib.projective_plane_incidence(d - 1))
        return best

    # D >= 4: W(q) for the largest prime power q with q+1 <= d, then spare-degree matching.
    if D >= 4:
        qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q) and q <= 7]
        if qs:
            n0, e0 = _gq_w(qs[0])
            e0 = _saturate_bip(n0, e0, d, n0 // 2, rng)
            consider((n0, e0))

    # Binary search on the half-order N of a bi-Cayley graph (order 2N).
    lo = max(d, best[0] // 2)
    hi = M // 2
    while lo < hi and time.monotonic() < deadline:
        mid = (lo + hi + 1) // 2
        now = time.monotonic()
        budget = max(1.0, (deadline - now) * 0.3)
        res = _attempt(mid, d, D, min(deadline, now + budget), rng)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = (res[0], list(res[1]))
            lo = mid
        else:
            hi = mid - 1

    return best
