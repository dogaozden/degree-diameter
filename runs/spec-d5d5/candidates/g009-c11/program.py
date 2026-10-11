import itertools
import math
import random
import time

import lib

ANNEAL_ITERS = 3000       # annealing steps per attempt
ATTEMPT_SECONDS = 1.5     # wall-clock budget per (base size, order) attempt
MAX_BASE = 4              # base orbits per side tried: a = 1..MAX_BASE
MAX_GROUPS_PER_ATTEMPT = 3


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
# Multi-orbit voltage lifts over semidirect products Z_m x| Z_k.
#
# New idea relative to the bi-Cayley search: the base graph has a orbits on
# each side (A_0..A_{a-1}, B_0..B_{a-1}). For a x a block pattern c[i][j]
# (nonnegative integers with all row and column sums equal to d), the block
# (i, j) carries a set S_ij of c[i][j] distinct group elements, and the lift has
#     A_{i,x} -- B_{j, x*s}   for every x in G and s in S_ij.
# Every A vertex then has degree sum_j c[i][j] = d and every B vertex has
# degree sum_i c[i][j] = d. Blocks are disjoint, so the lift is simple.
# Left multiplication is an automorphism, so the diameter is determined by the
# 2a orbit representatives A_{i,e} and B_{j,e}. The order is 2aN, so a = 2
# lets N reach about 85..170 for d = 5, D = 5, which is 4N in (340, 680].
# The block pattern is a sum of d random permutation matrices, which gives
# exact row and column sums of d.
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


def _random_pattern(a, d, rng):
    """Sum of d random permutation matrices: a nonnegative a x a matrix with all row/column sums d."""
    c = [[0] * a for _ in range(a)]
    for _ in range(d):
        perm = list(range(a))
        rng.shuffle(perm)
        for i in range(a):
            c[i][perm[i]] += 1
    return c


def _cost(a, N, T, sets, D):
    """Number of (source, vertex) pairs not within distance D, over the 2a orbit representatives."""
    V = 2 * a * N
    adj = [[] for _ in range(V)]
    for (i, j), S in sets.items():
        off = a * N + j * N
        for s in S:
            for x in range(N):
                u = i * N + x
                v = off + T[x][s]
                adj[u].append(v)
                adj[v].append(u)
    sources = [i * N for i in range(a)] + [a * N + j * N for j in range(a)]
    total = 0
    for src in sources:
        seen = bytearray(V)
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = 1
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(a, N, T, c, D, rng, deadline):
    """Anneal the block sets to zero unreached pairs; return the sets dict or None."""
    blocks = [(i, j) for i in range(a) for j in range(a) if c[i][j] > 0]
    sets = {key: rng.sample(range(N), c[key[0]][key[1]]) for key in blocks}
    cur = _cost(a, N, T, sets, D)
    for it in range(ANNEAL_ITERS):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / ANNEAL_ITERS))
        key = blocks[rng.randrange(len(blocks))]
        S = sets[key]
        k = rng.randrange(len(S))
        e = rng.randrange(N)
        if e in S:
            continue
        old = S[k]
        S[k] = e
        v = _cost(a, N, T, sets, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            S[k] = old
    return sets if cur == 0 else None


def _attempt(a, N, d, D, rng, deadline):
    """Try random groups of order N and random block patterns with base size a."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        _, mul, _ = lib.semidirect_group(m, k, r)
        T = [[mul(x, s) for s in range(N)] for x in range(N)]
        c = _random_pattern(a, d, rng)
        sets = _anneal(a, N, T, c, D, rng, deadline)
        if sets is not None:
            return T, sets
    return None


def _lift_edges(a, N, T, sets):
    """Expand the block sets into the full edge list on 2aN vertices."""
    edges = []
    for (i, j), S in sets.items():
        off = a * N + j * N
        for s in S:
            for x in range(N):
                edges.append((i * N + x, off + T[x][s]))
    return 2 * a * N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5 * time_limit, min(0.8 * time_limit, time_limit - 5.0))
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

    # Per base size a, an ascending pointer over the group order N.
    state = {}
    for a in range(1, MAX_BASE + 1):
        nmax = moore // (2 * a)
        if nmax <= d + 1:
            continue
        state[a] = {"N": max(d + 1, nmax // 2), "fails": 0, "ok": False, "nmax": nmax}

    while state and time.monotonic() < deadline:
        for a in list(state):
            if time.monotonic() >= deadline:
                break
            st = state[a]
            N = st["N"]
            if N > st["nmax"]:
                del state[a]
                continue
            att_deadline = min(deadline, time.monotonic() + ATTEMPT_SECONDS)
            res = _attempt(a, N, d, D, rng, att_deadline)
            if res is not None:
                T, sets = res
                n, e = _lift_edges(a, N, T, sets)
                consider(n, e)
                st["ok"] = True
                st["fails"] = 0
                st["N"] = N + 1
            else:
                st["fails"] += 1
                if st["fails"] >= 3:
                    st["fails"] = 0
                    if st["ok"]:
                        st["N"] = N + 1
                    else:
                        # No success yet for this base size: step the pointer down.
                        lower = max(d + 1, N - max(1, N // 10))
                        if lower == N:
                            del state[a]
                        else:
                            st["N"] = lower

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
