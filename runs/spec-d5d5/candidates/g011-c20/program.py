import math
import random
import time

import lib

MAX_GROUPS_PER_ATTEMPT = 12   # groups tried per (base size, order) within one attempt
ITERS = 300                   # annealing steps per (group, base-dart labelling) try
WINDOW0 = 24                  # first search window above the current best order
BUDGET0 = 0.4                 # seconds per candidate in the first round

# ----------------------------------------------------------------------------
# Idea: multi-vertex-base bi-lifts over finite groups.
#
# Base: a bipartite d-regular multigraph on p "A" vertices and p "B" vertices,
# with p*d darts (a, b). Each dart carries a group label g in G (|G| = N).
# Lift: fibre A_a = {(a, x)}, B_b = {(b, y)} for x, y in G; dart (a, b, g) joins
# (a, x) to (b, x*g) for every x. The lift has 2*p*N vertices and degree d.
#
# Left multiplication by h in G is an automorphism of the lift, so the
# eccentricity of every vertex equals that of (base vertex, identity) for its
# base vertex. Only 2p BFS runs are needed per evaluation.
#
# p = 1 is the bi-Cayley family used before. p = 2 and p = 3 give orders 4N and
# 6N for N in the range where a single fibre is too small to reach the record.
# The search uses a window above the current best order and grows it when a
# round fails.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when k = 1)."""
    if N in _GROUP_CACHE:
        return list(_GROUP_CACHE[N])
    out = []
    for k in range(1, N + 1):
        if N % k:
            continue
        m = N // k
        for r in range(m):
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                out.append((m, k, r))
    _GROUP_CACHE[N] = out
    return list(out)


_TABLE_CACHE = {}


def _table(N, m, k, r):
    """Multiplication table T[x][g] = x*g and inverse list for the group (identity is 0)."""
    key = (N, m, k, r)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]
    _, mul, inv = lib.semidirect_group(m, k, r)
    T = [[mul(x, g) for g in range(N)] for x in range(N)]
    invs = [inv(g) for g in range(N)]
    if len(_TABLE_CACHE) > 64:
        _TABLE_CACHE.clear()
    _TABLE_CACHE[key] = (T, invs)
    return T, invs


def _base(p, d, rng):
    """Random d-regular bipartite multigraph on p+p vertices: list of darts (a, b)."""
    a_seq = [i for i in range(p) for _ in range(d)]
    b_seq = [j for j in range(p) for _ in range(d)]
    rng.shuffle(b_seq)
    return list(zip(a_seq, b_seq))


def _adj(p, darts, labels, invs):
    """Base adjacency: outA[a] = [(b, g)], inB[b] = [(a, g^-1)]."""
    outA = [[] for _ in range(p)]
    inB = [[] for _ in range(p)]
    for (a, b), g in zip(darts, labels):
        outA[a].append((b, g))
        inB[b].append((a, invs[g]))
    return outA, inB


def _unreached(N, p, T, outA, inB, D):
    """Count pairs (source, vertex) not within distance D, over the 2p base sources at fibre identity."""
    V = 2 * p * N
    total = 0
    for s in range(2 * p):
        seen = bytearray(V)
        src = s * N
        seen[src] = 1
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                w, x = divmod(u, N)
                row = T[x]
                if w < p:
                    for b, g in outA[w]:
                        v = (p + b) * N + row[g]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
                else:
                    for a, gi in inB[w - p]:
                        v = a * N + row[gi]
                        if not seen[v]:
                            seen[v] = 1
                            nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += V - count
    return total


def _anneal(N, p, d, D, T, invs, darts, rng, iters, deadline):
    """Simulated annealing over dart labels to make the lift have diameter <= D."""
    labels = [rng.randrange(N) for _ in darts]
    outA, inB = _adj(p, darts, labels, invs)
    cur = _unreached(N, p, T, outA, inB, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        i = rng.randrange(len(darts))
        c = rng.randrange(N)
        if c == labels[i]:
            continue
        old = labels[i]
        labels[i] = c
        outA, inB = _adj(p, darts, labels, invs)
        v = _unreached(N, p, T, outA, inB, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            cur = v
        else:
            labels[i] = old
    return labels if cur == 0 else None


def _attempt(p, N, d, D, rng, deadline):
    """Try groups of order N with a random p-base until one labelling has diameter <= D."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS_PER_ATTEMPT]:
        if time.monotonic() > deadline:
            return None
        T, invs = _table(N, m, k, r)
        darts = _base(p, d, rng)
        labels = _anneal(N, p, d, D, T, invs, darts, rng, ITERS, deadline)
        if labels is not None:
            return T, darts, labels
    return None


def _edges(N, p, T, darts, labels):
    """Edge list of the lift; A fibres use indices 0..p-1, B fibres p..2p-1 (all A < all B)."""
    E = set()
    for (a, b), g in zip(darts, labels):
        for x in range(N):
            u = a * N + x
            v = (p + b) * N + T[x][g]
            E.add((u, v))
    return sorted(E)


# ----------------------------------------------------------------------------
# Baseline families.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
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

    best = (1, [])
    best_n = 1

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact record case: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            n, e = lib.araujo_lopez_graph(d - 2)
            consider(n, e)
        except ValueError:
            pass

    if D >= 2:
        consider(*lib.haar_graph(d, range(d)))
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if d < 2 or D < 2:
        return best

    moore = lib._moore_bound(d, D)

    # Candidates (order, p, N) with order = 2*p*N, bounded by the Moore bound.
    cands = []
    for p in (1, 2, 3):
        for N in range(d, moore // (2 * p) + 1):
            n2 = 2 * p * N
            if n2 <= moore:
                cands.append((n2, p, N))
    cands.sort()

    window = WINDOW0
    budget = BUDGET0
    while time.monotonic() < deadline:
        todo = [c for c in cands if best_n < c[0] <= best_n + window]
        if not todo:
            if not any(c[0] > best_n for c in cands):
                break
            window *= 2
            continue
        success = False
        for n2, p, N in todo:
            now = time.monotonic()
            if now >= deadline:
                break
            att_deadline = min(deadline, now + budget)
            res = _attempt(p, N, d, D, rng, att_deadline)
            if res is None:
                continue
            T, darts, labels = res
            edges = _edges(N, p, T, darts, labels)
            consider(2 * p * N, edges)
            success = True
            break
        if not success:
            budget *= 2
            window += WINDOW0

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
