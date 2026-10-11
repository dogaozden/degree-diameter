import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (unchanged from the parent; used as fallbacks and for
# calibration cases).
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
# Bolder search: tabu search over bi-Cayley lifts.
#
# Structure: k A-blocks and k B-blocks, each block a copy of a group G of
# order m*k2 (semidirect product Z_m x| Z_k2). Layer l pairs A-block i with
# B-block layers[l][i] through voltage S[l][i]: A_{i,g} ~ B_{p,g*s}. Each
# layer is a permutation, so every vertex has degree d and bipartiteness holds.
#
# Unlike the parent's annealing, this uses best-improvement tabu search:
# at each step a slot (layer, A-block) is chosen, a sample of candidate
# voltages is scored exactly, and the best non-tabu move is applied even if it
# worsens the cost. Random restarts break stagnation. The cost is the number
# of (representative, vertex) pairs at distance > D, plus a penalty for
# duplicate edges. Any solution is still checked with lib.is_valid.
# ----------------------------------------------------------------------------

_PEN = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(100):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12])
        m0 = max(2, -(-target // k2))
        m = m0 + rng.randrange(0, 4)
        if k2 == 1:
            return m, 1, 1
        if k2 == 2 and rng.random() < 0.4:
            r = m - 1
            if math.gcd(r, m) == 1 and (r * r) % m == 1 % m:
                return m, 2, r
            continue
        cands = [c for c in range(1, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e))."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when block-representative b is within distance D."""
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
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _dup(layers, S, k, d):
    """Number of duplicated (A-block, B-block, voltage) keys across layers."""
    keys = set()
    for l in range(d):
        for i in range(k):
            keys.add((i, layers[l][i], S[l][i]))
    return d * k - len(keys)


def _tabu(d, D, k, G, Ts, Invs, rng, deadline, max_iters):
    """Tabu search over voltages with random restarts. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    nbr = np.empty((d, N), dtype=np.int64)

    def fresh():
        layers = [rng.sample(range(k), k) for _ in range(d)]
        S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
        for l in range(d):
            for i in range(k):
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
        return layers, S

    def score(layers, S):
        reach = _reach(k, G, D, nbr, d)
        return _unreached(k, N, reach) + _PEN * _dup(layers, S, k, d), reach

    layers, S = fresh()
    cur, reach = score(layers, S)
    best = cur
    best_sol = ([r[:] for r in layers], [r[:] for r in S])
    tabu = {}
    stall = 0
    it = 0
    while cur > 0 and it < max_iters and time.monotonic() < deadline:
        it += 1
        bad = np.flatnonzero(reach != full)
        if bad.size and rng.random() < 0.6:
            u = int(bad[rng.randrange(bad.size)])
            blk = u // G
            if blk < k:
                i = blk
                l = rng.randrange(d)
            else:
                l = rng.randrange(d)
                i = layers[l].index(blk - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        cands = list(range(G)) if G <= 24 else rng.sample(range(G), 24)
        move_c = None
        move_s = None
        move_r = None
        for s in cands:
            if s == old:
                continue
            S[l][i] = s
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], s)
            c, r = score(layers, S)
            is_tabu = tabu.get((l, i, s), 0) > it
            if is_tabu and c >= best:
                continue
            if move_c is None or c < move_c or (c == move_c and rng.random() < 0.5):
                move_c, move_s, move_r = c, s, r

        if move_c is None:
            # Every candidate was tabu: take a random non-old voltage.
            choices = [s for s in range(G) if s != old]
            if not choices:
                S[l][i] = old
                _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)
                continue
            move_s = rng.choice(choices)
            S[l][i] = move_s
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], move_s)
            move_c, move_r = score(layers, S)
        else:
            S[l][i] = move_s
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], move_s)

        tabu[(l, i, old)] = it + 8 + rng.randrange(8)
        cur, reach = move_c, move_r
        if cur < best:
            best = cur
            best_sol = ([r[:] for r in layers], [r[:] for r in S])
            stall = 0
        else:
            stall += 1
        if stall > 300 and cur > 0:
            layers, S = fresh()
            cur, reach = score(layers, S)
            tabu.clear()
            stall = 0

    if best != 0:
        return None
    bl, bS = best_sol
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, bl[l][i], bS[l][i])
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Bipartition colouring and greedy pair insertion.
# ----------------------------------------------------------------------------

def _two_color(n, edges):
    """Return a proper 2-colouring (list of 0/1) of the graph, or None if it is not bipartite."""
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
    """Greedy pair insertion: grow the order by 2 while the result stays valid."""
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
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.8 * budget
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

    if D <= 2:
        return best

    # Tabu search over bi-Cayley lifts with a wider range of base sizes.
    while time.monotonic() < search_deadline:
        k = rng.choice([1, 2, 3, 4, 4, 5, 5, 6, 6, 7, 8])
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 25 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        per_deadline = min(search_deadline, time.monotonic() + 8.0)
        res = _tabu(d, D, k, G, Ts, Invs, rng, per_deadline, 3000)
        if res is not None:
            consider(res[0], res[1])

    # Greedy pair insertion on the best graph found so far.
    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
