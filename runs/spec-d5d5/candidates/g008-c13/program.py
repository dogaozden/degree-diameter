import itertools
import math
import random
import time

import lib

MAX_GROUPS = 12     # groups tried per (k, N) attempt
ITERS = 800         # annealing steps per (group, base graph) try


# ----------------------------------------------------------------------------
# Safe baseline families. Each is checked with lib.is_valid before use.
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
# Voltage lifts over small non-abelian groups.
#
# Base bipartite multigraph: k "A" vertices and k "B" vertices, every base
# vertex of degree d (so nd = d*k darts). Dart i joins A-vertex aend[i] to
# B-vertex bend[i] with voltage vg[i] in a group G of order N.
# Lift: vertices (u, x), u a base vertex, x in G. Dart (a, b, g) joins
# (a, x) to (b, x*g). Left multiplication by h is an automorphism of the lift,
# so eccentricities only need to be checked from the fibre identities (u, e).
# k = 1 is the bi-Cayley family (one base edge-bundle of d parallel darts).
# k > 1 gives larger orders 2kN from a richer base graph.
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


def _distinct(aend, bend, vg):
    """No two darts may share the same (A-end, B-end, voltage), else edges repeat."""
    return len(set(zip(aend, bend, vg))) == len(vg)


def _cost(k, N, D, aend, bend, vg, Tcol, ginv):
    """Total count of (source, vertex) pairs at distance > D, over the 2k fibre identities."""
    adj = [[] for _ in range(2 * k)]
    for i in range(len(vg)):
        a = aend[i]
        b = k + bend[i]
        g = vg[i]
        adj[a].append((b, Tcol[g]))
        adj[b].append((a, Tcol[ginv[g]]))
    M = 2 * k * N
    total = 0
    for s in range(2 * k):
        seen = bytearray(M)
        start = s * N           # fibre vertex (s, identity), identity has index 0
        seen[start] = 1
        frontier = [start]
        count = 1
        for _ in range(D):
            nxt = []
            for node in frontier:
                u, x = divmod(node, N)
                for v, tbl in adj[u]:
                    w = v * N + tbl[x]
                    if not seen[w]:
                        seen[w] = 1
                        nxt.append(w)
            if not nxt:
                break
            count += len(nxt)
            frontier = nxt
        total += M - count
    return total


def _anneal(k, d, N, D, Tcol, ginv, rng, iters, deadline):
    """Anneal base-graph endpoints and voltages until every fibre source reaches all vertices within D."""
    nd = d * k
    aend = [i // d for i in range(nd)]
    bend = [i // d for i in range(nd)]
    rng.shuffle(bend)                       # keeps every B-vertex at degree d
    vg = [rng.randrange(N) for _ in range(nd)]
    tries = 0
    while not _distinct(aend, bend, vg):
        vg = [rng.randrange(N) for _ in range(nd)]
        tries += 1
        if tries > 200:
            return None
    cur = _cost(k, N, D, aend, bend, vg, Tcol, ginv)
    for it in range(iters):
        if cur == 0:
            return bend, vg
        if time.monotonic() > deadline:
            break
        temp = max(0.05, 2.0 * (1.0 - it / iters))
        nb = bend[:]
        nv = vg[:]
        if k > 1 and rng.random() < 0.5:
            i, j = rng.sample(range(nd), 2)
            nb[i], nb[j] = nb[j], nb[i]     # rewire two darts' B-ends
        else:
            i = rng.randrange(nd)
            nv[i] = rng.randrange(N)        # change one voltage
        if not _distinct(aend, nb, nv):
            continue
        new = _cost(k, N, D, aend, nb, nv, Tcol, ginv)
        if new <= cur or rng.random() < math.exp(-(new - cur) / temp):
            bend, vg, cur = nb, nv, new
    return (bend, vg) if cur == 0 else None


def _attempt(k, d, D, N, rng, deadline):
    """Try groups of order N for base size k; return (n, edges) for a valid lift, or None."""
    groups = _groups(N)
    rng.shuffle(groups)
    for m, k2, r in groups[:MAX_GROUPS]:
        if time.monotonic() > deadline:
            return None
        _, mul, inv = lib.semidirect_group(m, k2, r)
        Tcol = [[mul(x, g) for x in range(N)] for g in range(N)]  # Tcol[g][x] = x*g
        ginv = [inv(g) for g in range(N)]
        res = _anneal(k, d, N, D, Tcol, ginv, rng, ITERS, deadline)
        if res is not None:
            bend, vg = res
            nd = d * k
            edges = []
            for i in range(nd):
                a = i // d
                b = k + bend[i]
                tbl = Tcol[vg[i]]
                for x in range(N):
                    edges.append((a * N + x, b * N + tbl[x]))
            return 2 * k * N, edges
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(0.5, min(0.8 * time_limit, time_limit - 5.0))
    deadline = start + total
    rng = random.Random(seed)

    best = (1, [])

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 1 or D < 1:
        return best
    if D == 1 or d == 1:
        consider(2, [(0, 1)])
        return best

    # Record-matching calibration: incidence graph of PG(2, d-1).
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        consider(n, e)
        return best

    # Safe fallbacks.
    consider(2 * d, [(i, d + j) for i in range(d) for j in range(d)])   # K_{d,d}, diameter 2
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Voltage-lift search over base sizes k = 1..4 (k = 1 is bi-Cayley).
    moore = lib._moore_bound(d, D)
    ks = (1, 2, 3, 4)
    Nk = {k: max(2, moore // (4 * k)) for k in ks}   # starts near the ambitious target
    budget = 0.8
    while time.monotonic() < deadline:
        any_open = False
        for k in (2, 1, 3, 4):
            now = time.monotonic()
            if now >= deadline:
                break
            N = max(Nk[k], best[0] // (2 * k) + 1)   # only sizes beating the current best
            if 2 * k * N > moore:
                continue
            any_open = True
            att = min(deadline, now + budget)
            res = _attempt(k, d, D, N, rng, att)
            if res is not None:
                consider(res[0], res[1])
                Nk[k] = N + 1
            else:
                Nk[k] = N
        if not any_open:
            break
        budget = min(budget * 1.5, 15.0)

    if not lib.is_valid(best[0], best[1], d, D):
        return 1, []
    return best
