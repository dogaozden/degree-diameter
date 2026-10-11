import itertools
import math
import random
import time

import lib

ITERS = 250           # annealing steps per (group, base graph) attempt
GROUP_TRIES = 4       # groups tried per sampled order before resampling
PARTITION_WEIGHTS = [2, 2, 3, 3, 4, 1]   # base-graph sizes p (p vertices per side)


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
# Groups: semidirect products Z_m x| Z_k of order N (r = 1 gives abelian ones).
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
# NEW: multi-vertex voltage lifts over random bipartite base multigraphs.
#
# Base graph: p "A" vertices and p "B" vertices, d darts. Darts are the union of
# d random perfect matchings between A and B, so every base vertex has degree d.
# Each dart (i, j) carries a group label g; the lift joins A_{i,x} -- B_{j, x g}.
# Labels on parallel darts (same i, j) are kept distinct, so the lift is simple.
# Left multiplication is an automorphism of the lift, so the diameter is decided
# by BFS from the identity copy of each of the 2p base vertices.
# ----------------------------------------------------------------------------

def _random_base(p, d, rng):
    """Darts as (i, j) pairs: d random perfect matchings between p A-vertices and p B-vertices."""
    darts = []
    for _ in range(d):
        perm = list(range(p))
        rng.shuffle(perm)
        for i in range(p):
            darts.append((i, perm[i]))
    return darts


def _init_labels(darts, N, rng):
    """Random group labels, distinct among darts sharing the same base pair."""
    labs = []
    for t, pair in enumerate(darts):
        taken = {labs[s] for s in range(t) if darts[s] == pair}
        c = rng.randrange(N)
        while c in taken:
            c = rng.randrange(N)
        labs.append(c)
    return labs


def _unreached(N, p, darts, labs, T, D):
    """Total count of (source, vertex) pairs not within distance D, over the 2p base identities."""
    V = 2 * p * N
    adj = [[] for _ in range(V)]
    for (i, j), g in zip(darts, labs):
        ba = i * N
        bb = p * N + j * N
        for x in range(N):
            a = ba + x
            b = bb + T[x][g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in range(0, V, N):
        seen = bytearray(V)
        seen[src] = 1
        count = 1
        frontier = [src]
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


def _anneal_labels(N, p, darts, labs, T, D, rng, iters, deadline):
    """Simulated annealing over group labels to zero unreached pairs; None on failure."""
    cur = _unreached(N, p, darts, labs, T, D)
    for it in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, 1.5 * (1.0 - it / iters))
        t = rng.randrange(len(darts))
        pair = darts[t]
        taken = {labs[s] for s in range(len(darts)) if s != t and darts[s] == pair}
        c = rng.randrange(N)
        if c in taken:
            continue
        old = labs[t]
        labs[t] = c
        v = _unreached(N, p, darts, labs, T, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            labs[t] = old
    return labs if cur == 0 else None


def _lift_edges(N, p, darts, labs, T):
    """Edge list of the lift: A ids 0..pN-1, B ids pN..2pN-1."""
    E = []
    for (i, j), g in zip(darts, labs):
        for x in range(N):
            E.append((i * N + x, p * N + j * N + T[x][g]))
    return 2 * p * N, E


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit - 1.0
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

    # Voltage-lift search over varied base graphs and semidirect groups.
    while time.monotonic() < deadline:
        ps = [p for p in (1, 2, 3, 4)
              if p <= d and best_n // (2 * p) + 1 <= moore // (2 * p)]
        if not ps:
            break
        choices = [p for p in PARTITION_WEIGHTS if p in ps]
        if not choices:
            choices = ps
        p = rng.choice(choices)

        lo = best_n // (2 * p) + 1
        hi = moore // (2 * p)
        N = min(hi, lo + rng.randrange(0, 4))
        N = max(N, d)
        if N < 1:
            continue

        groups = _groups(N)
        rng.shuffle(groups)
        for m, k, r in groups[:GROUP_TRIES]:
            if time.monotonic() > deadline:
                break
            order, mul, inv = lib.semidirect_group(m, k, r)
            T = [[mul(x, g) for g in range(N)] for x in range(N)]
            darts = _random_base(p, d, rng)
            labs = _init_labels(darts, N, rng)
            att_deadline = min(deadline, time.monotonic() + 8.0)
            res = _anneal_labels(N, p, darts, labs, T, D, rng, ITERS, att_deadline)
            if res is not None:
                n, e = _lift_edges(N, p, darts, res, T)
                consider(n, e)
                break

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
