import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (cheap, always valid for their diameter).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main construction: bi-Cayley (group-voltage) lifts over semidirect products
# Z_m x| Z_k2, searched by simulated annealing on the number of unreached
# (representative, vertex) pairs.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h.
# Dart (i, j, s) joins A_{i,g} to B_{j,g*s} for all g.
# Left multiplication by any h is an automorphism, so each class {A_i} and
# {B_j} is a single orbit. The graph has diameter <= D iff a BFS of depth D
# from each of the 2k representatives A_{i,e}, B_{j,e} reaches everything.
#
# Each A_i gets one dart per layer, and each layer is a permutation of the B
# side, so every vertex has degree exactly d.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9
_gcache = {}


def _group_cands(G):
    """All (m, k2, r) with m * k2 = G, m >= 2, defining Z_m x| Z_k2 with generator r."""
    if G in _gcache:
        return _gcache[G]
    out = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    _gcache[G] = out
    return out


def _cost(k, G, D, darts, perm, reps):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    keys = set()
    for i, j, s in darts:
        keys.add((i, j, s))
    if len(keys) < len(darts):
        return _BIG  # duplicate edges would break simplicity
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        pm = perm[s]
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += N - count
    return total


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages (and B-side assignments) for one group.

    Returns (best_cost, best_darts, perm). best_cost == 0 means a valid lift.
    """
    perm = [[mul(g, s) for g in range(G)] for s in range(G)]  # perm[s][g] = g*s
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])

    cur = _cost(k, G, D, darts, perm, reps)
    best_c = cur
    best_d = [list(x) for x in darts]
    T0, T1 = 3.0, 0.2

    for it in range(iters):
        if best_c == 0:
            break
        if (it & 31) == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)

        if k > 1 and rng.random() < 0.25:
            # Swap the B-targets of two darts in the same layer (keeps B-degrees).
            L = rng.randrange(d)
            a = L * k + rng.randrange(k)
            b = L * k + rng.randrange(k)
            if a == b:
                continue
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            c2 = _cost(k, G, D, darts, perm, reps)
            if c2 <= cur or rng.random() < math.exp((cur - c2) / T):
                cur = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
        else:
            # Change one voltage.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            new = rng.randrange(G)
            if new == old:
                continue
            darts[idx][2] = new
            c2 = _cost(k, G, D, darts, perm, reps)
            if c2 <= cur or rng.random() < math.exp((cur - c2) / T):
                cur = c2
            else:
                darts[idx][2] = old

        if cur < best_c:
            best_c = cur
            best_d = [list(x) for x in darts]

    return best_c, best_d, perm


def _edges(k, G, darts, perm):
    E = set()
    for i, j, s in darts:
        pm = perm[s]
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    moore = lib._moore_bound(d, D)

    # Main search. Stop early when the best graph already meets the Moore bound
    # (calibration cases d3D3, d5D3, d5D4 finish instantly this way).
    fails = 0
    while time.monotonic() < deadline and best_n < moore:
        k = rng.choice([1, 1, 1, 1, 2, 2, 3])
        Gmin = best_n // (2 * k) + 1
        Gmax = moore // (2 * k)
        if Gmin > Gmax:
            ks = [kk for kk in (1, 2, 3) if best_n // (2 * kk) + 1 <= moore // (2 * kk)]
            if not ks:
                break
            continue
        G = Gmin + rng.randrange(0, min(4, Gmax - Gmin + 1))
        cands = _group_cands(G)
        if not cands:
            fails += 1
            continue
        m, k2, r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue

        c, darts, perm = _anneal(d, D, k, order, mul, rng, deadline, 3000)
        if c == 0:
            n, e = _edges(k, order, darts, perm)
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
