import itertools
import math
import random
import time

import numpy as np

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


def _search(d, D, k, G, rng, iters, deadline):
    """Simulated annealing over voltages in a group of order about G.

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
        i, j, _old = darts[idx]
        old_pm = perms[idx]
        new_pm = [mul(x, new_s) for x in range(G)]
        base_b = (k + j) * G
        for x in range(G):
            a = i * G + x
            ob = base_b + old_pm[x]
            nb_ = base_b + new_pm[x]
            adj[a].remove(ob)
            adj[ob].remove(a)
            adj[a].append(nb_)
            adj[nb_].append(a)
        darts[idx][2] = new_s
        perms[idx] = new_pm

    cost = _cost(k, G, D, adj)
    best_cost = cost
    best_darts = [list(x) for x in darts]
    best_perms = list(perms)

    T0 = 3.0
    for t in range(iters):
        if best_cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (1.0 - t / iters) + 0.05
        idx = rng.randrange(len(darts))
        i, j, old_s = darts[idx]
        new_s = rng.randrange(G)
        if new_s == old_s or (i, j, new_s) in keys:
            continue
        set_dart(idx, new_s)
        keys.discard((i, j, old_s))
        keys.add((i, j, new_s))
        c2 = _cost(k, G, D, adj)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best_cost:
                best_cost = cost
                best_darts = [list(x) for x in darts]
                best_perms = list(perms)
        else:
            set_dart(idx, old_s)
            keys.discard((i, j, new_s))
            keys.add((i, j, old_s))

    if best_cost != 0:
        return None
    E = set()
    for (i, j, _s), pm in zip(best_darts, best_perms):
        for x in range(G):
            E.add((i * G + x, (k + j) * G + pm[x]))
    return N, sorted(E)


# ----------------------------------------------------------------------------
# New construction for d = 6, D = 5: bipartite switch-annealing.
#
# Start from a Haar graph (circulant bipartite, 6-regular, simple), then keep
# the graph 6-regular and bipartite by random 2-switches:
#   a1-b1, a2-b2  ->  a1-b2, a2-b1   (only if the new edges are absent).
# Cost = number of ordered vertex pairs at distance > D, computed with
# bit-packed numpy reachability (D rounds of OR over neighbour rows).
# Cost 0 means diameter <= D. The side size N is climbed one step at a time.
# ----------------------------------------------------------------------------

def _d6_cost_fn(n, d, D):
    W = (n + 63) // 64
    ident = np.zeros((n, W), dtype=np.uint64)
    v = np.arange(n)
    ident[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)

    def cost(nbm):
        R = ident
        for _ in range(D):
            Rn = R.copy()
            for s in range(d):
                Rn |= R[nbm[:, s]]
            R = Rn
        pop = int(np.unpackbits(R.view(np.uint8)).sum())
        return n * n - pop

    return cost


def _d6_anneal(N, d, D, rng, t_end, init):
    """Anneal a d-regular bipartite graph with N + N vertices. Returns (best_cost, best_nb)."""
    n = 2 * N
    if init is None:
        nb = np.empty((n, d), dtype=np.int64)
        ar = np.arange(N)
        for s in range(d):
            nb[:N, s] = N + (ar + s) % N
            nb[N:, s] = (ar - s) % N
    else:
        nb = init.copy()

    adjM = np.zeros((N, N), dtype=bool)
    adjM[np.arange(N)[:, None], nb[:N] - N] = True

    cost = _d6_cost_fn(n, d, D)
    cur = cost(nb)
    best = cur
    bestnb = nb.copy()

    t0 = time.monotonic()
    span = max(1e-3, t_end - t0)
    T_hi, T_lo = 3.0, 0.2
    T = T_hi
    it = 0
    while cur > 0:
        if (it & 15) == 0:
            now = time.monotonic()
            if now >= t_end:
                break
            frac = (now - t0) / span
            T = T_hi * (T_lo / T_hi) ** frac
        it += 1

        a1 = rng.randrange(N)
        s1 = rng.randrange(d)
        b1 = int(nb[a1, s1])
        a2 = rng.randrange(N)
        s2 = rng.randrange(d)
        b2 = int(nb[a2, s2])
        if a1 == a2 or b1 == b2:
            continue
        if adjM[a1, b2 - N] or adjM[a2, b1 - N]:
            continue

        t1 = int(np.nonzero(nb[b1] == a1)[0][0])
        t2 = int(np.nonzero(nb[b2] == a2)[0][0])

        nb[a1, s1] = b2
        nb[a2, s2] = b1
        nb[b1, t1] = a2
        nb[b2, t2] = a1
        adjM[a1, b1 - N] = False
        adjM[a2, b2 - N] = False
        adjM[a1, b2 - N] = True
        adjM[a2, b1 - N] = True

        c2 = cost(nb)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
            cur = c2
            if cur < best:
                best = cur
                bestnb = nb.copy()
        else:
            nb[a1, s1] = b1
            nb[a2, s2] = b2
            nb[b1, t1] = a1
            nb[b2, t2] = a2
            adjM[a1, b2 - N] = False
            adjM[a2, b1 - N] = False
            adjM[a1, b1 - N] = True
            adjM[a2, b2 - N] = True

    return best, bestnb


def _d6_edges(N, d, nbm):
    return [(a, int(nbm[a, s])) for a in range(N) for s in range(d)]


def _build_d6d5(seed, time_limit, deadline):
    d, D = 6, 5
    rng = random.Random(seed)
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    N = 120
    slice_len = 6.0
    warm = None
    while time.monotonic() < deadline:
        t_end = min(deadline, time.monotonic() + slice_len)
        c, nbst = _d6_anneal(N, d, D, rng, t_end, warm)
        if c == 0:
            edges = _d6_edges(N, d, nbst)
            n = 2 * N
            if n > best_n and lib.is_valid(n, edges, d, D):
                best = (n, edges)
                best_n = n
            N += 1
            warm = None
        else:
            warm = nbst
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

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

    if d == 6 and D == 5:
        d6_deadline = start + min(0.8 * time_limit, time_limit - 6.0)
        try:
            res = _build_d6d5(seed, time_limit, d6_deadline)
        except Exception:
            res = None
        if res is not None and lib.is_valid(res[0], res[1], d, D):
            return res
        return lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    while time.monotonic() < deadline:
        k = rng.choice([1, 1, 1, 2, 2, 3])
        base = best_n // (2 * k)
        spread = max(3, base // 12)
        G = max(2, base + 1 + rng.randrange(spread))
        try:
            res = _search(d, D, k, G, rng, 2500, deadline)
        except Exception:
            res = None
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
