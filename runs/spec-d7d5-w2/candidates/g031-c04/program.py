import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or safe baseline families (fallbacks, always checked with lib.is_valid).
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
# New construction: general bipartite voltage lifts over Z_m x| Z_k2.
#
# Base multigraph: k A-vertices and k B-vertices, each of degree d, with
# darts (i, j, s). Dart t sits in A-block t // d. The lift has vertices
# A_{i,x} = i*G + x and B_{j,h} = (k+j)*G + h, and dart (i,j,s) joins
# A_{i,x} to B_{j, x*s}. Unlike layered permutations, the base multigraph is
# arbitrary: its B-endpoints are moved by 2-switches (swap the B-ends of two
# darts), which keep every base degree at d. Voltages are changed one at a time.
#
# Cost = (unreached representative pairs) + penalty * (duplicate darts).
# Simulated annealing minimises the cost. A zero-cost lift is a valid
# diameter-D bipartite graph with exact degree d, which is then checked with
# lib.is_valid. Greedy pair insertion runs afterwards.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _build_nbr(k, G, d, Ts, Invs, DJ, DS):
    """Neighbour table nbr[slot, vertex] for the lift of the dart base graph.

    Dart t = i*d + l belongs to A-block i in slot l. Each B-block j has exactly d
    incoming darts, listed by argsort order and reshaped to (k, d).
    """
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    idx = np.arange(k, dtype=np.int64)
    order2 = np.argsort(DJ, kind="stable").reshape(k, d)
    for l in range(d):
        t = idx * d + l
        s = DS[t]
        nbr[l, :k * G] = ((k + DJ[t])[:, None] * G + Ts[s]).reshape(-1)
        tt = order2[:, l]
        ai = tt // d
        nbr[l, k * G:] = (ai[:, None] * G + Invs[DS[tt]]).reshape(-1)
    return nbr


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G] = 1 << b
    for _ in range(D):
        new = reach.copy()
        for l in range(d):
            new |= reach[nbr[l]]
        if np.array_equal(new, reach):
            break
        reach = new
    return reach


def _edges_from(nbr, N, d):
    es = set()
    for l in range(d):
        for u, v in zip(range(N), nbr[l].tolist()):
            es.add((u, v) if u < v else (v, u))
    return sorted(es)


def _anneal(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over dart base graphs. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1  # noqa: F841 (kept for clarity of the reach encoding)
    tot = k * d
    perm = list(range(tot))
    rng.shuffle(perm)
    DJ = np.repeat(np.arange(k, dtype=np.int64), d)[np.array(perm, dtype=np.int64)]
    DS = np.array([rng.randrange(G) for _ in range(tot)], dtype=np.int64)

    def evaluate():
        nbr = _build_nbr(k, G, d, Ts, Invs, DJ, DS)
        reach = _reach(k, G, D, nbr, d)
        keys = {(t // d, int(DJ[t]), int(DS[t])) for t in range(tot)}
        dup = tot - len(keys)
        c = 2 * k * N - int(_POP[reach].sum()) + _PENALTY * dup
        return int(c), reach

    cost, reach = evaluate()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))
        if rng.random() < 0.4:
            # 2-switch on B-endpoints of two darts: keeps all base degrees.
            t1, t2 = rng.randrange(tot), rng.randrange(tot)
            if DJ[t1] == DJ[t2]:
                continue
            DJ[t1], DJ[t2] = DJ[t2], DJ[t1]
            c2, r2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                DJ[t1], DJ[t2] = DJ[t2], DJ[t1]
        else:
            # Voltage change on one dart.
            t1 = rng.randrange(tot)
            old = int(DS[t1])
            new = rng.randrange(G)
            if new == old:
                continue
            DS[t1] = new
            c2, r2 = evaluate()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
            else:
                DS[t1] = old

    if cost != 0:
        return None
    nbr = _build_nbr(k, G, d, Ts, Invs, DJ, DS)
    return N, _edges_from(nbr, N, d)


# ----------------------------------------------------------------------------
# Bipartition colouring and greedy pair insertion.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    adj = lib.adjacency(n, edges)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _extend(n, edges, d, D, rng, deadline):
    """Greedy pair insertion: grow the order by 2 per accepted step, checked by lib.is_valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    while time.monotonic() < deadline:
        order = list(range(len(edges)))
        rng.shuffle(order)
        chosen = []
        used_a, used_b = set(), set()
        for t in order:
            if len(chosen) == d - 1:
                break
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            if a in used_a or b in used_b:
                continue
            chosen.append(t)
            used_a.add(a)
            used_b.add(b)
        if len(chosen) < d - 1:
            break
        x, y = n, n + 1
        cs = set(chosen)
        cand = [e for t, e in enumerate(edges) if t not in cs]
        for t in chosen:
            u, v = edges[t]
            a, b = (u, v) if color[u] == 0 else (v, u)
            cand.append((x, b))
            cand.append((y, a))
        cand.append((x, y))
        if lib.is_valid(n + 2, cand, d, D):
            edges = cand
            n += 2
            color.extend([0, 1])
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.85 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bandit over base sizes k, with the new dart-lift annealer.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    while time.monotonic() < search_deadline:
        if rng.random() < 0.25:
            k = rng.choice(_KS)
        else:
            k = max(_KS, key=lambda kk: (wins[kk] + 1) / (trials[kk] + 2) + 0.02 * rng.random())
        base_G = -(-(best_n + 2) // (2 * k))
        target = base_G + rng.randrange(0, max(2, best_n // (40 * 2 * k) + 2))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _anneal(d, D, k, G, Ts, Invs, rng, search_deadline, 8000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Greedy pair insertion on the best graph found.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
