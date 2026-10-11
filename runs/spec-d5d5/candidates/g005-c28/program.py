import itertools
import math
import random
import time

import lib

ITERS = 1200                  # annealing steps per restart
T_HOT = 1.5                   # initial annealing temperature (unreached-pair units)
T_COLD = 0.15                 # final annealing temperature
WINDOW = 10                   # frontier candidates considered at once
BASE_BUDGET = 0.3             # seconds per attempt, grows with failures
TIME_FRAC = 0.8               # fraction of time_limit we are willing to use


# ----------------------------------------------------------------------------
# Baseline families (fast, validated before use).
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Multi-orbit bi-Cayley (voltage) lifts over non-cyclic groups.
#
# Base graph: a "A" orbits and a "B" orbits, each orbit a copy of a group G of
# order N. A_{i,x} is joined to B_{j,x*g} for every g in blocks[i][j]. Left
# multiplication is an automorphism, so distances from one identity vertex per
# orbit (2a sources) decide the diameter. Row and column sums of the block
# sizes equal d, so the lift is d-regular and bipartite by construction.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k."""
    if N in _GROUP_CACHE:
        return _GROUP_CACHE[N]
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return out


def _matrix(a, d):
    """a x a nonnegative integer matrix with all row and column sums equal to d (circulant)."""
    if a == 1:
        return [[d]]
    if a == 2:
        c0 = (d + 1) // 2
        c1 = d // 2
        return [[c0, c1], [c1, c0]]
    c = [d // 3 + (1 if t < d % 3 else 0) for t in range(3)]
    return [[c[(j - i) % 3] for j in range(3)] for i in range(3)]


def _adjacency(a, N, T, invs, blocks):
    """Neighbour lists for the lift. A-orbit i has indices i*N + x; B-orbit j has a*N + j*N + y."""
    fwd = [[] for _ in range(a)]
    bwd = [[] for _ in range(a)]
    for i in range(a):
        for j in range(a):
            for g in blocks[i][j]:
                fwd[i].append((j, g))
                bwd[j].append((i, invs[g]))
    nbr = [None] * (2 * a * N)
    for i in range(a):
        base_i = i * N
        for x in range(N):
            row = T[x]
            nbr[base_i + x] = [a * N + j * N + row[g] for j, g in fwd[i]]
    for j in range(a):
        base_j = a * N + j * N
        for y in range(N):
            row = T[y]
            nbr[base_j + y] = [i * N + row[ig] for i, ig in bwd[j]]
    return nbr


def _unreached(a, N, nbr, D):
    """Count (source, vertex) pairs not within distance D, over one source per orbit."""
    total = 2 * a * N
    srcs = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    bad = 0
    for src in srcs:
        seen = bytearray(total)
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in nbr[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        bad += total - count
    return bad


def _search(a, N, M, D, rng, deadline):
    """Random restarts of annealing over block contents until a diameter-D lift is found or time runs out."""
    groups = _groups(N)
    if not groups:
        return None
    while time.monotonic() < deadline:
        m, k, r = rng.choice(groups)
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        blocks = [[(rng.sample(range(N), M[i][j]) if M[i][j] else [])
                   for j in range(a)] for i in range(a)]
        cur = _unreached(a, N, _adjacency(a, N, T, invs, blocks), D)
        for it in range(ITERS):
            if cur == 0:
                return blocks, T
            if time.monotonic() > deadline:
                return None
            temp = T_HOT * (T_COLD / T_HOT) ** (it / ITERS)
            i = rng.randrange(a)
            j = rng.randrange(a)
            if not blocks[i][j]:
                continue
            kk = rng.randrange(len(blocks[i][j]))
            c = rng.randrange(N)
            if c in blocks[i][j]:
                continue
            old = blocks[i][j][kk]
            blocks[i][j][kk] = c
            v = _unreached(a, N, _adjacency(a, N, T, invs, blocks), D)
            if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
                cur = v
            else:
                blocks[i][j][kk] = old
        if cur == 0:
            return blocks, T
    return None


def _edges(a, N, blocks, T):
    """Explicit edge list of the lift; distinct (i, j, g) give distinct edges."""
    E = []
    for i in range(a):
        for j in range(a):
            for g in blocks[i][j]:
                for x in range(N):
                    E.append((i * N + x, a * N + j * N + T[x][g]))
    return E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    t_end = start + TIME_FRAC * time_limit
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
    else:
        if D >= 2:
            consider(*lib.haar_graph(d, range(d)))
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
        if D >= 4 and time.monotonic() < t_end:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])

        if d >= 2 and D >= 2:
            Mmoore = lib._moore_bound(d, D)
            Ms = {}
            cands = []
            for a in (1, 2, 3):
                Ms[a] = _matrix(a, d)
                for N in range(2, Mmoore // (2 * a) + 1):
                    V = 2 * a * N
                    if best_n < V <= Mmoore:
                        cands.append((V, a, N))
            cands.sort()
            tries = {}

            while time.monotonic() < t_end and cands:
                window = cands[:WINDOW]
                c = min(window, key=lambda x: (tries.get(x, 0), x[0]))
                V, a, N = c
                now = time.monotonic()
                budget = min(t_end - now, BASE_BUDGET * (1 + 0.5 * tries.get(c, 0)))
                if budget <= 0:
                    break
                res = _search(a, N, Ms[a], D, rng, now + budget)
                if res is not None:
                    blocks, T = res
                    consider(V, _edges(a, N, blocks, T))
                    cands = [x for x in cands if x != c and x[0] > best_n]
                else:
                    tries[c] = tries.get(c, 0) + 1

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
