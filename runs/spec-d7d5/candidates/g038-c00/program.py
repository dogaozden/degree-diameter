import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and near-exact baselines (unchanged from the parent).
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


def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# New search: greedy-then-anneal over bi-Cayley lifts.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, group G of order
# G = m*k2 (semidirect Z_m x| Z_k2, r = 1 gives the direct product).
# Each layer l is a perfect matching A_i -> B_{layers[l][i]} with voltage s:
# A_{i,g} ~ B_{j, g*s}. Every vertex then has degree exactly d.
#
# Unlike the parent (random restarts of annealing), each attempt here first
# builds voltages greedily: entries are chosen one at a time to minimise the
# number of (representative, vertex) pairs left beyond distance D, using only
# the entries placed so far (unplaced entries are self-loops, harmless to the
# reachability sweep). The greedy assignment then seeds a simulated-annealing
# polish. Distinct (i, j, s) keys guarantee a simple graph.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_SAMPLE = 150


def _sample_group(G, rng):
    """Return (m, k2, r) with m*k2 == G for the semidirect product Z_m x| Z_k2."""
    divs = [t for t in range(1, min(G, 40) + 1) if G % t == 0]
    k2 = rng.choice(divs)
    m = G // k2
    r = 1 % m if m > 0 else 0
    if k2 > 1 and m > 2 and rng.random() < 0.7:
        for _ in range(60):
            c = rng.randrange(2, m)
            if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                r = c
                break
    return m, k2, r


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


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Layer l: A-block i is matched to B-block j with voltage s (both directions)."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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


def _unreached(k, N, reach):
    """Number of (representative, vertex) pairs at distance more than D."""
    return 2 * k * N - int(_POP[reach].sum())


def _polish(d, D, k, G, Ts, Invs, layers, S, nbr, used, rng, deadline, iters):
    """Simulated annealing on single voltages, keeping keys (i, j, s) unique."""
    N = 2 * k * G
    cost = _unreached(k, N, _reach(k, G, D, nbr, d))
    c0 = float(max(cost, 1))
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        i = rng.randrange(k)
        j = layers[l][i]
        old = S[l][i]
        new = rng.randrange(G)
        if new == old or (i, j, new) in used:
            continue
        used.discard((i, j, old))
        used.add((i, j, new))
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, j, new)
        c2 = _unreached(k, N, _reach(k, G, D, nbr, d))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            used.discard((i, j, new))
            used.add((i, j, old))
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, j, old)
    return cost


def _run(d, D, k, G, Ts, Invs, rng, deadline):
    """One greedy construction followed by polish. Returns (n, edges) if valid, else None."""
    N = 2 * k * G
    if rng.random() < 0.5:
        layers = [rng.sample(range(k), k) for _ in range(d)]
    else:
        layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    nbr = np.tile(np.arange(N, dtype=np.int64), (d, 1))  # placeholders: self-loops
    S = [[0] * k for _ in range(d)]
    used = set()

    for l in range(d):
        for i in range(k):
            if time.monotonic() > deadline:
                return None
            j = layers[l][i]
            best_s, best_c = None, None
            for s in rng.sample(range(G), min(G, _SAMPLE)):
                if (i, j, s) in used:
                    continue
                _set_dart(nbr, k, G, Ts, Invs, l, i, j, s)
                c = _unreached(k, N, _reach(k, G, D, nbr, d))
                if best_c is None or c < best_c or (c == best_c and rng.random() < 0.5):
                    best_c, best_s = c, s
            if best_s is None:
                for s in range(G):
                    if (i, j, s) not in used:
                        best_s = s
                        break
            if best_s is None:
                return None
            S[l][i] = best_s
            used.add((i, j, best_s))
            _set_dart(nbr, k, G, Ts, Invs, l, i, j, best_s)

    cost = _polish(d, D, k, G, Ts, Invs, layers, S, nbr, used, rng, deadline, 8000)
    if cost != 0:
        return None
    edges = [(u, int(nbr[l, u])) for u in range(k * G) for l in range(d)]
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    final_deadline = start + max(1.0, time_limit - 4.0)
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

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: target graphs just above the current best order.
    if D >= 3 and d >= 3:
        while time.monotonic() < deadline:
            k = rng.choice([1, 1, 2, 2, 3, 4])
            lo = best_n // (2 * k) + 1
            G = lo + rng.randrange(0, max(2, lo // 8))
            m, k2, r = _sample_group(G, rng)
            G, Ts, Invs = _semidirect_tables(m, k2, r)
            res = _run(d, D, k, G, Ts, Invs, rng, deadline)
            if res is not None:
                consider(res[0], res[1])

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
