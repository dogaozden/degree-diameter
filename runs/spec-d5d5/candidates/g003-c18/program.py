import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products, searched by annealing.
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2k representatives reaches everything.
#
# New in this version:
#   * Bounded-cost evaluation. Metropolis acceptance is decided up front by
#     drawing a threshold thr = cost - T*ln(U). The cost sum over
#     representatives stops as soon as it exceeds the threshold, so rejected
#     moves are cheap.
#   * Layer-swap move. Exchanging the B-targets of two darts in the same layer
#     keeps every B vertex at degree d, so it explores a different neighbourhood
#     from re-drawing voltages.
#   * Time-based geometric cooling, so each annealing run uses its whole slice.
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _cost_bounded(k, G, D, darts, perms, limit):
    """Unreached (representative, vertex) pairs, stopping early once the total exceeds limit.

    Returns the exact cost when it is <= limit, and some value > limit otherwise.
    """
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        ba = i * G
        bb = (k + j) * G
        for g in range(G):
            a = ba + g
            b = bb + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = bytearray(N)
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
        total += N - count
        if total > limit:
            return total
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, rp, rng, deadline):
    """Metropolis annealing over darts until cost 0 or the deadline.

    Returns (best_cost, best_darts). Each dart is [i, j, s]; each layer of k darts
    is a permutation, so every A and every B has degree d.
    """
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [rp[s] for _, _, s in darts]
    N = 2 * k * G
    cost = _cost_bounded(k, G, D, darts, perms, 10 * _BIG)
    best_cost = cost
    best_darts = [x[:] for x in darts]

    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    T0 = max(2.0, 0.02 * N)
    T1 = 0.5
    while cost > 0:
        now = time.monotonic()
        if now >= deadline:
            break
        frac = (now - t0) / span
        T = T0 * (T1 / T0) ** frac
        thr = cost - T * math.log(max(rng.random(), 1e-12))
        limit = int(thr)

        if k > 1 and rng.random() < 0.5:
            # Layer-swap: exchange the B-targets of two darts in one layer.
            layer = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            a = layer * k + i1
            b = layer * k + i2
            darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
            c2 = _cost_bounded(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[a][1], darts[b][1] = darts[b][1], darts[a][1]
        else:
            # Voltage move: re-draw the group element of one dart.
            idx = rng.randrange(len(darts))
            old = darts[idx][2]
            oldp = perms[idx]
            new = rng.randrange(G)
            darts[idx][2] = new
            perms[idx] = rp[new]
            c2 = _cost_bounded(k, G, D, darts, perms, limit)
            if c2 <= limit:
                cost = c2
            else:
                darts[idx][2] = old
                perms[idx] = oldp

        if cost < best_cost:
            best_cost = cost
            best_darts = [x[:] for x in darts]

    return best_cost, best_darts


def _search(d, D, k, G, rng, deadline):
    """One annealing run over a random group of order G. Returns (n, edges) or None."""
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    rp = [[mul(x, s) for x in range(G)] for s in range(G)]
    cost, darts = _anneal(d, D, k, G, rp, rng, deadline)
    if cost == 0:
        perms = [rp[s] for _, _, s in darts]
        return _edges(k, G, darts, perms)
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, 0.82 * time_limit - 1.5)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
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

    slice_len = max(3.0, 0.15 * time_limit)
    while time.monotonic() < deadline - 0.5:
        k = rng.choice([1, 1, 2, 2, 3, 4])
        need = best_n // (2 * k) + 1  # ensures 2*k*G > best_n
        G = max(2, need + rng.randrange(0, 4))
        sub = min(deadline, time.monotonic() + slice_len)
        res = _search(d, D, k, G, rng, sub)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
