import itertools
import math
import random
import time

import lib

# New idea: multi-orbit bi-Cayley voltage lifts. The base graph has K orbits on
# each side, with a degree-split matrix shape[i][j] = |S_ij| (row and column sums
# equal d). Vertex A_{i,x} is joined to B_{j,x*g} for g in S_ij. Left
# multiplication is an automorphism, so only the K A-sources and K B-sources at
# the identity need BFS. K=2 gives 4N-vertex graphs, a finer search grid than the
# 2N-vertex K=1 family. Candidates are tried in ascending order of order.

ITERS = 300
GROUPS_PER_TRY = 25
INIT_BUDGET = 1.0
CAP_FRACTION = 0.6


# ----------------------------------------------------------------------------
# Baseline families (unchanged from the parent).
# ----------------------------------------------------------------------------

def _best_pg(d):
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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


def _best_gq(d):
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group enumeration and shape choices.
# ----------------------------------------------------------------------------

def _groups(N):
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _shapes(d):
    """Degree-split patterns as (K, shape). Each row and column of shape sums to d."""
    out = [(1, [[d]])]
    if d >= 2:
        p = (d + 1) // 2
        out.append((2, [[p, d - p], [d - p, p]]))
        if d - 1 != p and d - 1 >= 1:
            out.append((2, [[d - 1, 1], [1, d - 1]]))
    return out


# ----------------------------------------------------------------------------
# Multi-orbit lift cost and annealing.
# ----------------------------------------------------------------------------

def _build_darts(sets, invs, K):
    dA = [[] for _ in range(K)]
    dB = [[] for _ in range(K)]
    for i in range(K):
        for j in range(K):
            for g in sets[i][j]:
                dA[i].append((j, g))
                dB[j].append((i, invs[g]))
    return dA, dB


def _cost(N, T, K, dA, dB, D):
    """Total unreached (source, vertex) pairs over the K A-sources and K B-sources."""
    KN = K * N
    V = 2 * KN
    srcs = [i * N for i in range(K)] + [(K + j) * N for j in range(K)]
    total = 0
    for src in srcs:
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                if u < KN:
                    i, x = divmod(u, N)
                    row = T[x]
                    for j, g in dA[i]:
                        v = (K + j) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    j, y = divmod(u - KN, N)
                    row = T[y]
                    for i, h in dB[j]:
                        v = i * N + row[h]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += V - count
    return total


def _anneal(N, T, invs, K, shape, D, rng, iters, deadline):
    sets = [[rng.sample(range(N), shape[i][j]) for j in range(K)] for i in range(K)]
    dA, dB = _build_darts(sets, invs, K)
    cur = _cost(N, T, K, dA, dB, D)
    slots = [(i, j) for i in range(K) for j in range(K) if shape[i][j] > 0]
    for it in range(iters):
        if cur == 0:
            break
        if (it & 15) == 0 and time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i, j = rng.choice(slots)
        s = sets[i][j]
        t = rng.randrange(len(s))
        c = rng.randrange(N)
        if c in s:
            continue
        old = s[t]
        s[t] = c
        dA2, dB2 = _build_darts(sets, invs, K)
        v = _cost(N, T, K, dA2, dB2, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
            dA, dB = dA2, dB2
        else:
            s[t] = old
    return sets if cur == 0 else None


def _attempt(N, K, shape, d, D, rng, deadline):
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:GROUPS_PER_TRY]:
        if time.monotonic() >= deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        sets = _anneal(N, T, invs, K, shape, D, rng, ITERS, deadline)
        if sets is not None:
            edges = []
            for i in range(K):
                for j in range(K):
                    for x in range(N):
                        for g in sets[i][j]:
                            edges.append((i * N + x, (K + j) * N + T[x][g]))
            return 2 * K * N, edges
    return None


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + min(0.85 * time_limit, time_limit - 3.0)
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
    cap = int(CAP_FRACTION * moore)

    cands = []
    for K, shape in _shapes(d):
        n_min = max(max(row) for row in shape)
        n_min = max(n_min, 2)
        for N in range(n_min, cap // (2 * K) + 2):
            total = 2 * K * N
            if best_n < total <= cap:
                cands.append((total, K, shape, N))
    cands.sort(key=lambda c: (c[0], c[1]))

    budget = INIT_BUDGET
    while cands and time.monotonic() < deadline:
        progressed = False
        for cand in list(cands):
            if time.monotonic() >= deadline:
                break
            total, K, shape, N = cand
            if total <= best_n:
                continue
            now = time.monotonic()
            res = _attempt(N, K, shape, d, D, rng, min(deadline, now + budget))
            if res is not None:
                n, e = res
                consider(n, e)
                progressed = True
        cands = [c for c in cands if c[0] > best_n]
        if not progressed:
            budget *= 1.5

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
