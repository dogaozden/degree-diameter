import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (used as fallbacks and for calibration cases).
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
# Bi-Cayley / group-voltage lifts over semidirect products.
#
# Vertices: A_{i,g} = i*G + g and B_{j,h} = (k+j)*G + h, base size k per side.
# Dart (i, j, s) joins A_{i,x} to B_{j, x*s} for every x in the group.
# Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
# depth D from each of the 2k representatives reaches every vertex.
# Each A_i (and each B_j) has exactly d darts, so the lift is d-regular and
# bipartite, and the no-duplicate condition is that (i, j, s) keys are distinct.
#
# Search: simulated annealing over the voltages with a repaired cost that counts
# unreached (representative, vertex) pairs. Each attempt draws a fresh group.
# ----------------------------------------------------------------------------

_GROUP_CACHE = {}


def _groups_of_order(G):
    """All semidirect products Z_m x| Z_k2 with m * k2 = G, as (m, k2, r) triples (r = 1 for k2 = 1)."""
    if G in _GROUP_CACHE:
        return _GROUP_CACHE[G]
    out = []
    for k2 in range(1, min(G, 40) + 1):
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            out.append((m, 1, 1))
            continue
        for r in range(1, m):
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                out.append((m, k2, r))
    _GROUP_CACHE[G] = out
    return out


def _cost(k, G, D, adj):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    N = len(adj)
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
    return total


def _search(d, D, k, G, mul, rng, iters, deadline):
    """Annealing over voltages in a group of order G with base size k.

    Returns (n, edges) with diameter <= D and max degree d, or None.
    """
    N = 2 * k * G
    keys = set()
    darts = []
    for p in [rng.sample(range(k), k) for _ in range(d)]:
        for i in range(k):
            j = p[i]
            s = None
            for _ in range(300):
                c = rng.randrange(G)
                if (i, j, c) not in keys:
                    s = c
                    break
            if s is None:
                return None
            keys.add((i, j, s))
            darts.append([i, j, s])

    perms = [[mul(x, s) for x in range(G)] for _, _, s in darts]
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        bb = (k + j) * G
        for x in range(G):
            a = i * G + x
            b = bb + pm[x]
            adj[a].append(b)
            adj[b].append(a)

    cost = _cost(k, G, D, adj)
    best_cost = cost
    best_darts = [list(x) for x in darts]

    T0 = 2.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        i, j, old = darts[idx]
        new = rng.randrange(G)
        if new == old or (i, j, new) in keys:
            continue
        old_pm = perms[idx]
        new_pm = [mul(x, new) for x in range(G)]
        bb = (k + j) * G
        for x in range(G):
            a = i * G + x
            ob = bb + old_pm[x]
            nb = bb + new_pm[x]
            adj[a].remove(ob)
            adj[ob].remove(a)
            adj[a].append(nb)
            adj[nb].append(a)
        c2 = _cost(k, G, D, adj)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            keys.discard((i, j, old))
            keys.add((i, j, new))
            darts[idx][2] = new
            perms[idx] = new_pm
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
        else:
            for x in range(G):
                a = i * G + x
                ob = bb + old_pm[x]
                nb = bb + new_pm[x]
                adj[a].remove(nb)
                adj[nb].remove(a)
                adj[a].append(ob)
                adj[ob].append(a)

    if best_cost != 0:
        return None
    E = set()
    for i, j, s in best_darts:
        bb = (k + j) * G
        for x in range(G):
            E.add((i * G + x, bb + mul(x, s)))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(float(time_limit), 60.0)
    deadline = start + max(0.5, 0.8 * budget - 1.0)
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

    # Search only where it can help (D >= 4); calibration cases return instantly.
    if D >= 4 and d >= 3:
        while time.monotonic() < deadline:
            k = 1 if rng.random() < 0.7 else 2
            Gmin = best_n // (2 * k) + 1
            G = Gmin + rng.randrange(3)
            grps = _groups_of_order(G)
            if not grps:
                continue
            m, k2, r = rng.choice(grps)
            try:
                _, mul, _ = lib.semidirect_group(m, k2, r)
                res = _search(d, D, k, G, mul, rng, 3000, deadline)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
