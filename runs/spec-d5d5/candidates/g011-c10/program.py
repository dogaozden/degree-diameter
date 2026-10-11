"""Bi-Cayley-style 2x2 base lifts over semidirect products.

New idea (not in the parent): instead of one A-fibre and one B-fibre, use a
2x2 base multigraph. The graph has A-fibres A_0, A_1 and B-fibres B_0, B_1,
each a copy of a group G of order N. Dart (i, j, g) joins A_i(x) to B_j(x*g)
for all x in G. A count matrix C = [[a, d-a], [d-a, a]] gives every vertex
degree d. The graph has 4N vertices, is bipartite, and left multiplication is
an automorphism, so the diameter test only needs BFS from the four base
vertices at the identity. Those four sources are run together as one numpy
array, which keeps the annealing cost low. A frontier-walking search raises
N one step at a time with growing budgets.
"""
import math
import random
import time

import numpy as np

import lib

MAX_GROUPS_PER_ATTEMPT = 10
ITERS = 5000
WINDOW = 3
_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) giving groups Z_m x|_r Z_k of order N."""
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    return out


def _tables(key):
    """Per-group permutation arrays PERMS[g][x] = x*g and inverse table, cached."""
    if key not in _CACHE:
        m, k, r = key
        order, mul, inv = lib.semidirect_group(m, k, r)
        N = m * k
        T = np.array([[mul(x, g) for g in range(N)] for x in range(N)], dtype=np.int64)
        PERMS = [np.ascontiguousarray(T[:, g]) for g in range(N)]
        invs = [inv(g) for g in range(N)]
        _CACHE[key] = (PERMS, invs)
    return _CACHE[key]


def _configs(d):
    """Count matrices with row and column sums d (up to swapping B-fibres)."""
    return [(2, 2, [[a, d - a], [d - a, a]]) for a in range(1, d // 2 + 1)]


def _ops(darts, p, PERMS, invs):
    """Directed transition list (source base, target base, permutation)."""
    ops = []
    for i, j, g in darts:
        ops.append((i, p + j, PERMS[g]))
        ops.append((p + j, i, PERMS[invs[g]]))
    return ops


def _cost(N, nb, ops, D):
    """Number of (source, vertex) pairs not within distance D, sources = identity of each base vertex."""
    R = np.zeros((nb, nb, N), dtype=bool)
    idx = np.arange(nb)
    R[idx, idx, 0] = True
    for _ in range(D):
        NR = R.copy()
        for b, tb, perm in ops:
            NR[:, tb, perm] |= R[:, b, :]
        if np.array_equal(NR, R):
            break
        R = NR
    return nb * nb * N - int(np.count_nonzero(R))


def _anneal(p, q, C, N, PERMS, invs, D, rng, deadline, iters):
    """Anneal the group elements on darts until the diameter bound holds or time runs out."""
    nb = p + q
    darts = []
    chosen = {}
    for i in range(p):
        for j in range(q):
            c = C[i][j]
            if c <= 0:
                continue
            gs = rng.sample(range(N), c)
            chosen[(i, j)] = set(gs)
            for g in gs:
                darts.append([i, j, g])
    if not darts:
        return None
    cur = _cost(N, nb, _ops(darts, p, PERMS, invs), D)
    it = 0
    while cur > 0 and it < iters:
        if time.monotonic() >= deadline:
            return None
        it += 1
        k = rng.randrange(len(darts))
        i, j, old = darts[k]
        new = rng.randrange(N)
        if new in chosen[(i, j)]:
            continue
        darts[k][2] = new
        v = _cost(N, nb, _ops(darts, p, PERMS, invs), D)
        temp = max(0.3, 2.0 * (1.0 - it / iters))
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            chosen[(i, j)].discard(old)
            chosen[(i, j)].add(new)
            cur = v
        else:
            darts[k][2] = old
    if cur == 0:
        return [tuple(x) for x in darts]
    return None


def _attempt(N, cfgs, D, rng, deadline):
    """Try groups of order N and count matrices until one gives diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for key in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() >= deadline:
            return None
        PERMS, invs = _tables(key)
        order = list(cfgs)
        rng.shuffle(order)
        for p, q, C in order:
            if time.monotonic() >= deadline:
                return None
            darts = _anneal(p, q, C, N, PERMS, invs, D, rng, deadline, ITERS)
            if darts is not None:
                return p, q, darts, PERMS
    return None


def _edges(N, p, q, darts, PERMS):
    """Expand darts into the full edge list on (p+q)*N vertices."""
    edges = []
    for i, j, g in darts:
        perm = PERMS[g].tolist()
        base_a = i * N
        base_b = (p + j) * N
        for x in range(N):
            edges.append((base_a + x, base_b + perm[x]))
    return (p + q) * N, edges


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d-1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []

    best = [(1, [])]

    def consider(n, e):
        ok = lib.is_valid(n, e, d, D)
        if ok and n > best[0][0]:
            best[0] = (n, e)
        return ok

    # Record-matching case for D = 3.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best[0]

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))

    if d >= 2 and D >= 2:
        cfgs = _configs(d)
        hi = lib._moore_bound(d, D) // 4   # 2x2 base lift has 4N vertices
        best_N = d - 1
        budget = 0.4
        while time.monotonic() < deadline and best_N < hi:
            found = False
            top = min(hi, best_N + WINDOW)
            for N in range(best_N + 1, top + 1):
                now = time.monotonic()
                if now >= deadline:
                    break
                att = min(deadline, now + budget)
                res = _attempt(N, cfgs, D, rng, att)
                if res is None:
                    continue
                p, q, darts, PERMS = res
                n, edges = _edges(N, p, q, darts, PERMS)
                if consider(n, edges):
                    best_N = N
                    found = True
                    break
            if not found:
                budget *= 2

    if not lib.is_valid(best[0][0], best[0][1], d, D):
        return 1, []
    return best[0]
