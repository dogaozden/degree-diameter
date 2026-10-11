import itertools
import math
import random
import time

import lib

MAX_GROUPS_PER_CONFIG = 12    # groups tried for one (b, N) configuration per slice
ITERS = 1500                  # annealing steps per (group, base lift) try
WINDOW = 24                   # how far above the current best order to search
MAX_B = 5                     # maximum number of base vertices per side
INIT_SLICE = 0.15             # seconds per configuration in the first pass


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
# Groups: semidirect products Z_m x| Z_k of order N (cyclic when k = 1).
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


# ----------------------------------------------------------------------------
# NEW: multi-orbit voltage lifts with a regular base multigraph.
#
# Base: b vertices A_0..A_{b-1} and b vertices B_0..B_{b-1}. The base is d-regular
# on both sides: for each layer k there is a permutation sig[k] of range(b), and
# dart (i, sig[k][i], g) with voltage g in G. The lift has vertices A(i,x), B(j,y)
# for x, y in G, and edges A(i,x) -- B(j, x*g) for every dart (i, j, g).
# Left multiplication by G is an automorphism, so it suffices to BFS from the 2b
# sources A(i,e) and B(j,e) to decide the diameter.
# ----------------------------------------------------------------------------

def _lift_cost(b, N, T, invs, d, D, sig, gel):
    """Total unreached (source, vertex) pairs over the 2b sources, plus a penalty per duplicate dart."""
    bN = b * N
    V = 2 * bN
    invsig = [[0] * b for _ in range(d)]
    for k in range(d):
        for i in range(b):
            invsig[k][sig[k][i]] = i
    dups = 0
    for i in range(b):
        for k1 in range(d):
            for k2 in range(k1 + 1, d):
                if sig[k1][i] == sig[k2][i] and gel[k1][i] == gel[k2][i]:
                    dups += 1
    adj = [None] * V
    for i in range(b):
        base_i = i * N
        for x in range(N):
            adj[base_i + x] = [bN + sig[k][i] * N + T[x][gel[k][i]] for k in range(d)]
    for j in range(b):
        base_j = bN + j * N
        for y in range(N):
            adj[base_j + y] = [invsig[k][j] * N + T[y][invs[gel[k][invsig[k][j]]]]
                               for k in range(d)]
    total = 0
    sources = [i * N for i in range(b)] + [bN + j * N for j in range(b)]
    for s in sources:
        seen = bytearray(V)
        seen[s] = 1
        frontier = [s]
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
    return total + 1000 * dups


def _anneal_lift(b, N, T, invs, d, D, rng, iters, deadline):
    """Anneal over layer permutations and voltages to make the lift have diameter <= D."""
    sig = []
    for _ in range(d):
        p = list(range(b))
        rng.shuffle(p)
        sig.append(p)
    gel = [[rng.randrange(N) for _ in range(b)] for _ in range(d)]
    cur = _lift_cost(b, N, T, invs, d, D, sig, gel)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 3.0 * (1.0 - it / iters))
        if b == 1 or rng.random() < 0.6:
            k = rng.randrange(d)
            i = rng.randrange(b)
            old = gel[k][i]
            new = rng.randrange(N)
            if new == old:
                continue
            gel[k][i] = new
            c = _lift_cost(b, N, T, invs, d, D, sig, gel)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                gel[k][i] = old
        else:
            k = rng.randrange(d)
            i1, i2 = rng.sample(range(b), 2)
            sig[k][i1], sig[k][i2] = sig[k][i2], sig[k][i1]
            c = _lift_cost(b, N, T, invs, d, D, sig, gel)
            if c <= cur or rng.random() < math.exp(-(c - cur) / temp):
                cur = c
            else:
                sig[k][i1], sig[k][i2] = sig[k][i2], sig[k][i1]
    if cur == 0:
        return sig, gel
    return None


def _lift_edges(b, N, T, d, sig, gel):
    """Materialise the lift as (n, edges)."""
    bN = b * N
    edges = set()
    for k in range(d):
        for i in range(b):
            j = sig[k][i]
            g = gel[k][i]
            for x in range(N):
                edges.add((i * N + x, bN + j * N + T[x][g]))
    return 2 * bN, sorted(edges)


def _try_config(b, N, d, D, rng, deadline):
    """Try groups of order N for a b-vertex base lift; return (N, T, sig, gel) on success."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_CONFIG]:
        if time.monotonic() >= deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal_lift(b, N, T, invs, d, D, rng, ITERS, deadline)
        if res is not None:
            sig, gel = res
            return N, T, sig, gel
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 3.0))
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
            return True
        return False

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
    slice_s = INIT_SLICE
    try:
        while time.monotonic() < deadline:
            lo = best_n + 2
            hi = min(moore, best_n + WINDOW)
            if lo > hi:
                break
            accepted = False
            for V in range(lo, hi + 1, 2):
                for b in range(1, MAX_B + 1):
                    if V % (2 * b):
                        continue
                    N = V // (2 * b)
                    now = time.monotonic()
                    if now >= deadline:
                        break
                    res = _try_config(b, N, d, D, rng, min(deadline, now + slice_s))
                    if res is None:
                        continue
                    N_, T, sig, gel = res
                    n, e = _lift_edges(b, N_, T, d, sig, gel)
                    if consider(n, e):
                        accepted = True
                        break
                if accepted or time.monotonic() >= deadline:
                    break
            if not accepted:
                slice_s *= 2
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
