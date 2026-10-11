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
# Group-voltage lifts over semidirect products (bi-Cayley graphs).
#
# Vertices: A_i,g = i*G + g  and  B_j,h = (k+j)*G + h, for base size k.
# Dart (i, j, s) joins A_i,g to B_j,g*s for every g in the group.
#
# Left multiplication by any h is an automorphism, so each class A_i and B_j is
# one orbit. Hence the graph has diameter <= D iff, for each of the 2k base
# representatives, a BFS of depth D reaches every vertex.
#
# NEW in this version: "missed-class guided" moves. The evaluation reports which
# vertices are still unreached from the representatives. A dart touching the
# base class of a missed vertex is then preferred for mutation, and each
# proposal is chosen as the best of a few candidate voltages (a small greedy
# line search) before the annealing acceptance test is applied.
# ----------------------------------------------------------------------------

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


def _ball(src, D, adj, N):
    """Bytearray marking all vertices within distance D of src."""
    seen = bytearray(N)
    seen[src] = 1
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
        frontier = nxt
    return seen


def _evaluate(k, G, D, adj):
    """Return (cost, missed).

    cost   = number of (representative, vertex) pairs not reached within distance D.
    missed = a sample of vertices unreached from some representative (guides moves).
    """
    N = len(adj)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    missed = []
    for src in reps:
        seen = _ball(src, D, adj, N)
        total += N - seen.count(1)
        if len(missed) < 48:
            for v in range(N):
                if not seen[v]:
                    missed.append(v)
                    if len(missed) >= 48:
                        break
    return total, missed


def _pick_dart(darts, k, G, missed, rng):
    """Choose a dart index, preferring darts incident to a base class with missed vertices."""
    if missed and rng.random() < 0.6:
        w = rng.choice(missed)
        c = w // G
        if c < k:
            cand = [t for t, (i, _j, _s) in enumerate(darts) if i == c]
        else:
            cand = [t for t, (_i, j, _s) in enumerate(darts) if j == c - k]
        if cand:
            return rng.choice(cand)
    return rng.randrange(len(darts))


def _search(d, D, k, G, rng, iters, deadline):
    """Annealing over voltages with best-of-C candidate line search per step.

    Returns (n, edges) with diameter <= D and max degree d, or None.
    """
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    G = order
    if k * G < d:
        return None
    N = 2 * k * G

    keys = set()
    darts = []
    for p in [rng.sample(range(k), k) for _ in range(d)]:
        for i in range(k):
            j = p[i]
            s = rng.randrange(G)
            tries = 0
            while (i, j, s) in keys and tries < 50:
                s = rng.randrange(G)
                tries += 1
            if (i, j, s) in keys:
                return None
            keys.add((i, j, s))
            darts.append([i, j, s])

    perms = [[mul(x, s) for x in range(G)] for _, _, s in darts]
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_b = (k + j) * G
        for x in range(G):
            a = i * G + x
            b = base_b + pm[x]
            adj[a].append(b)
            adj[b].append(a)

    def set_dart(idx, new_s):
        """Change dart idx to voltage new_s, updating perms and adj in place."""
        i, j, _old = darts[idx]
        old_pm = perms[idx]
        new_pm = [mul(x, new_s) for x in range(G)]
        base_b = (k + j) * G
        for x in range(G):
            a = i * G + x
            ob = base_b + old_pm[x]
            nb = base_b + new_pm[x]
            adj[a].remove(ob)
            adj[ob].remove(a)
            adj[a].append(nb)
            adj[nb].append(a)
        darts[idx][2] = new_s
        perms[idx] = new_pm

    cost, missed = _evaluate(k, G, D, adj)
    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    C = 2  # candidate voltages per step (greedy line search)
    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = _pick_dart(darts, k, G, missed, rng)
        i, j, old_s = darts[idx]

        cand_best = None
        for _ in range(C):
            new_s = rng.randrange(G)
            if new_s == old_s or (i, j, new_s) in keys:
                continue
            set_dart(idx, new_s)
            c2, m2 = _evaluate(k, G, D, adj)
            set_dart(idx, old_s)
            if cand_best is None or c2 < cand_best[0]:
                cand_best = (c2, new_s, m2)
        if cand_best is None:
            continue

        c2, new_s, m2 = cand_best
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            set_dart(idx, new_s)
            keys.discard((i, j, old_s))
            keys.add((i, j, new_s))
            cost = c2
            missed = m2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)

    if best_cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(best_darts, best_perms):
        for x in range(G):
            E.add((i * G + x, (k + j) * G + pm[x]))
    return N, sorted(E)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
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

    # Main search: annealed group voltage lifts with 1-3 base vertices per side.
    # Each success raises best_n, so the target group order climbs naturally.
    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        spread = max(3, base // 12)
        G = max(2, base + 1 + rng.randrange(spread))
        try:
            res = _search(d, D, k, G, rng, 1500, deadline)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
