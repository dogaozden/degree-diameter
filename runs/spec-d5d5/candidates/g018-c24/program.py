import itertools
import math
import random
import time

import lib

ITERS = 1500          # annealing steps per (group, base-lift) try
MAX_GROUPS = 6       # groups tried per (t, N) attempt
KEY_WINDOW = 16      # number of smallest untried candidate orders attempted per round


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
# Group enumeration.
# ----------------------------------------------------------------------------

def _groups(N):
    """Semidirect parameters (m, k, r) with m*k = N, giving Z_m x|_r Z_k (cyclic when r = 1, k = 1)."""
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
# New construction: layered base lifts.
#
# A base bipartite multigraph has t "A" vertices and t "B" vertices, and is
# d-regular. It is given by d permutations P[i] of range(t): layer i joins A_u
# to B_{P[i][u]}. Each dart (layer i, vertex u) carries a voltage V[i][u] in a
# finite group G of order N. The lift has vertices A_{u,x}, B_{v,y} for x,y in G
# and edges A_{u,x} -- B_{P[i][u], x*V[i][u]}. This is a bipartite d-regular graph
# on 2tN vertices. Left multiplication is an automorphism, so distances from the
# 2t sources (base vertex, identity) decide the diameter.
#
# Parent code used only t = 1 (bi-Cayley). Here t ranges over 1..6, and the
# annealer moves both voltages and the base permutations.
# ----------------------------------------------------------------------------

def _unreached_lift(t, N, T, invs, P, V, d, D):
    """Total (source, vertex) pairs not within distance D, summed over the 2t identity sources."""
    Anb = [[(t + P[i][u], V[i][u]) for i in range(d)] for u in range(t)]
    Bnb = [[] for _ in range(t)]
    for i in range(d):
        for u in range(t):
            Bnb[P[i][u]].append((u, invs[V[i][u]]))
    size = 2 * t * N
    total = 0
    for s in range(2 * t):
        seen = bytearray(size)
        src = s * N
        seen[src] = 1
        count = 1
        frontier = [src]
        for _ in range(D):
            nxt = []
            for idx in frontier:
                b, x = divmod(idx, N)
                row = T[x]
                if b < t:
                    for tb, g in Anb[b]:
                        j = tb * N + row[g]
                        if not seen[j]:
                            seen[j] = 1
                            nxt.append(j)
                else:
                    for u, ig in Bnb[b - t]:
                        j = u * N + row[ig]
                        if not seen[j]:
                            seen[j] = 1
                            nxt.append(j)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += size - count
    return total


def _anneal_lift(t, N, T, invs, d, D, rng, iters, deadline):
    """Anneal voltages and base permutations until the lift has diameter <= D. Return (P, V) or None."""
    P = [rng.sample(range(t), t) for _ in range(d)]
    V = [[rng.randrange(N) for _ in range(t)] for _ in range(d)]
    cur = _unreached_lift(t, N, T, invs, P, V, d, D)
    for it in range(iters):
        if cur == 0:
            break
        if time.monotonic() > deadline:
            return None
        temp = max(0.05, 3.0 * (1.0 - it / iters))
        P2 = [row[:] for row in P]
        V2 = [row[:] for row in V]
        i = rng.randrange(d)
        if t > 1 and rng.random() < 0.25:
            a, b = rng.sample(range(t), 2)
            P2[i][a], P2[i][b] = P2[i][b], P2[i][a]
        else:
            u = rng.randrange(t)
            V2[i][u] = rng.randrange(N)
        v = _unreached_lift(t, N, T, invs, P2, V2, d, D)
        if v <= cur or rng.random() < math.exp(-(v - cur) / temp):
            P, V, cur = P2, V2, v
    if cur == 0:
        return P, V
    return None


def _attempt(t, N, d, D, rng, deadline, iters):
    """Try groups of order N for base size t until one lift has diameter <= D or time runs out."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        order, mul, inv = lib.semidirect_group(m, k, r)
        T = [[mul(x, g) for g in range(N)] for x in range(N)]
        invs = [inv(g) for g in range(N)]
        res = _anneal_lift(t, N, T, invs, d, D, rng, iters, deadline)
        if res is not None:
            P, V = res
            return t, N, T, P, V
    return None


def _lift_edges(t, N, T, d, P, V):
    """Edge list of the layered lift: A vertices are 0..tN-1, B vertices tN..2tN-1."""
    edges = set()
    for x in range(N):
        row = T[x]
        for u in range(t):
            a = u * N + x
            for i in range(d):
                b = (t + P[i][u]) * N + row[V[i][u]]
                edges.add((a, b))
    return 2 * t * N, sorted(edges)


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

    Moore = lib._moore_bound(d, D)

    # Candidate keys (order, t, N) with order = 2tN <= Moore bound, sorted ascending.
    keys = []
    for o in range(3, Moore + 1):
        for t in range(1, 7):
            if o % (2 * t) == 0:
                N = o // (2 * t)
                if N >= 2:
                    keys.append((o, t, N))
    keys.sort()

    budget = 0.4
    while time.monotonic() < deadline:
        pool = [key for key in keys if key[0] > best_n][:KEY_WINDOW]
        if not pool:
            break
        for o, t, N in pool:
            if o <= best_n:
                continue
            now = time.monotonic()
            if now >= deadline:
                break
            res = _attempt(t, N, d, D, rng, min(deadline, now + budget), ITERS)
            if res is None:
                continue
            tt, NN, T, P, V = res
            n_out, edges = _lift_edges(tt, NN, T, d, P, V)
            consider(n_out, edges)
        budget *= 2

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
