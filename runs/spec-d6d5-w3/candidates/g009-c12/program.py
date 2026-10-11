import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Algebraic baselines: projective plane, Araujo-Pardo-Lopez (D = 3) and the
# generalized quadrangle W(q) (D >= 4). Used as safe starting points.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo-Lopez graph for d = q + 2 with q a prime power >= 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 7 for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# New family: bi-regular cyclic voltage lifts with k base vertices per side.
#
# Vertices: A_{i,x} = i*G + x and B_{j,y} = (k+j)*G + y, x, y in Z_G.
# Each of the d "layers" is a permutation p of {0..k-1}; it contributes the
# darts (i, p[i], s) meaning A_{i,x} ~ B_{p[i], x+s}. Each layer gives every
# A-orbit and every B-orbit exactly one dart, so the lift is d-regular.
#
# Because Z_G acts by translation on each side, distances from A_{i,0} and
# B_{j,0} determine the diameter. The cost is the number of unreached pairs
# from those 2k representatives. Zero cost means diameter <= D.
# Search is simulated annealing over the voltages.
# ----------------------------------------------------------------------------

def _lift_edges(k, G, darts):
    E = set()
    for i, j, s in darts:
        for x in range(G):
            a = i * G + x
            b = (k + j) * G + (x + s) % G
            E.add((a, b))
    return 2 * k * G, sorted(E)


def _lift_cost(k, G, D, darts):
    """Number of (representative, vertex) pairs at distance > D. Zero means diameter <= D."""
    if len(set(darts)) < len(darts):
        return 10 ** 9
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for i, j, s in darts:
        bi = i * G
        bj = (k + j) * G
        for x in range(G):
            a = bi + x
            b = bj + (x + s) % G
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
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
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _random_darts(d, k, G, rng):
    darts = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        for i in range(k):
            darts.append((i, p[i], rng.randrange(G)))
    return darts


def _anneal_lift(d, D, k, G, rng, deadline, iters):
    """Anneal voltages for one (k, G). Returns darts with cost 0, or None."""
    darts = _random_darts(d, k, G, rng)
    cost = _lift_cost(k, G, D, darts)
    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.998)
        idx = rng.randrange(len(darts))
        i, j, s = darts[idx]
        new = list(darts)
        if rng.random() < 0.8:
            new[idx] = (i, j, rng.randrange(G))
        else:
            # Swap the B-targets of two darts in the same layer (keeps regularity).
            layer = idx // k
            a = layer * k + rng.randrange(k)
            b = layer * k + rng.randrange(k)
            if a == b:
                continue
            ia, ja, sa = new[a]
            ib, jb, sb = new[b]
            new[a] = (ia, jb, sa)
            new[b] = (ib, ja, sb)
        c2 = _lift_cost(k, G, D, new)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            darts, cost = new, c2
    return darts if cost == 0 else None


def _lift_search(d, D, best_n, rng, deadline, consider):
    """Repeatedly try cyclic lifts with order just above the current best. Returns nothing."""
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 2, 2, 3])
        lo = max(2, (best_n + 1) // (2 * k) + 1)
        hi = lo + max(2, lo // 12)
        G = rng.randint(lo, hi)
        darts = _anneal_lift(d, D, k, G, rng, deadline, 2500)
        if darts is None:
            continue
        n, e = _lift_edges(k, G, darts)
        if consider(n, e):
            best_n = n


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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
            return True
        return False

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
        ar = _araujo(d)
        if ar is not None:
            consider(ar[0], ar[1])

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Bold new search: annealed bi-regular cyclic lifts, aimed above the best so far.
    if D >= 3:
        _lift_search(d, D, best_n, rng, deadline, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
