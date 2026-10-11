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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{p,g*s}.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)
_KS = (1, 2, 3, 4)


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
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _make_nbr(k, G, Ts, Invs, d, layers, S):
    """Build the (d, N) neighbour table of a bi-Cayley lift from layers and voltages."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])
    return nbr


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b is set when representative block b is within distance D."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and layer swaps.

    Returns (N, adj, unreached) for the best duplicate-free state seen, where adj is an
    (N, d) array of neighbours, or None if no duplicate-free state was reached.
    """
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = _make_nbr(k, G, Ts, Invs, d, layers, S)

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    best_unr = None
    best_snap = None

    def snap(unr, dup):
        nonlocal best_unr, best_snap
        if dup == 0 and (best_unr is None or unr < best_unr):
            best_unr = unr
            best_snap = ([row[:] for row in layers], [row[:] for row in S])

    reach = _reach(k, G, D, nbr, d)
    cur_unr = _unreached(k, N, reach)
    cur_dup = dupcount()
    cost = cur_unr + _PENALTY * cur_dup
    c0 = float(max(cost, 1))
    snap(cur_unr, cur_dup)

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        x = rng.random()

        if k >= 2 and x < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            u2 = _unreached(k, N, r2)
            d2 = dupcount()
            c2 = u2 + _PENALTY * d2
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach, cur_unr, cur_dup = c2, r2, u2, d2
                snap(cur_unr, cur_dup)
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.4 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        u2 = _unreached(k, N, r2)
        d2 = dupcount()
        c2 = u2 + _PENALTY * d2
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach, cur_unr, cur_dup = c2, r2, u2, d2
            snap(cur_unr, cur_dup)
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if best_snap is None:
        return None
    lb, sb = best_snap
    nbr_b = _make_nbr(k, G, Ts, Invs, d, lb, sb)
    return N, nbr_b.T.copy(), best_unr


# ----------------------------------------------------------------------------
# NEW: packed full-graph distance cost and 2-switch annealing repair.
#
# Works on any d-regular bipartite graph given as an (N, d) neighbour array with
# side A = vertices 0..nA-1 and side B = the rest. A 2-switch replaces edges
# (a1,b1),(a2,b2) by (a1,b2),(a2,b1); it keeps regularity and bipartiteness.
# The cost is the number of ordered vertex pairs at distance > D, computed with
# packed bitsets over all N vertices (not only block representatives).
# ----------------------------------------------------------------------------

def _packed_cost(adj, D):
    """Return the number of ordered pairs at distance > D (0 iff the graph has diameter <= D)."""
    N, d = adj.shape
    W = (N + 7) // 8
    idx = np.arange(N, dtype=np.int64)
    R = np.zeros((N, W), dtype=np.uint8)
    R[idx, idx >> 3] = np.left_shift(1, idx & 7).astype(np.uint8)
    for _ in range(D):
        new = R.copy()
        for s in range(d):
            new |= R[adj[:, s]]
        if np.array_equal(new, R):
            break
        R = new
    reached = int(_POP8[R].sum())
    return N * N - reached


def _switch_repair(adj, nA, D, rng, deadline):
    """2-switch simulated annealing that tries to drive the distance cost to zero.

    Returns (best_cost, best_adj).
    """
    N, d = adj.shape
    adj = adj.copy()
    cost = _packed_cost(adj, D)
    best, best_adj = cost, adj.copy()
    t_begin = time.monotonic()
    total = max(1e-3, deadline - t_begin)
    while cost > 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t_begin) / total
        T = max(0.3, 3.0 * (1.0 - frac))
        a1 = rng.randrange(nA)
        p = rng.randrange(d)
        a2 = rng.randrange(nA)
        q = rng.randrange(d)
        b1 = int(adj[a1, p])
        b2 = int(adj[a2, q])
        if a1 == a2 or b1 == b2:
            continue
        if np.any(adj[a1] == b2) or np.any(adj[a2] == b1):
            continue
        s1 = int(np.flatnonzero(adj[b1] == a1)[0])
        s2 = int(np.flatnonzero(adj[b2] == a2)[0])
        adj[a1, p] = b2
        adj[a2, q] = b1
        adj[b1, s1] = a2
        adj[b2, s2] = a1
        c2 = _packed_cost(adj, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            if cost < best:
                best = cost
                best_adj = adj.copy()
        else:
            adj[a1, p] = b1
            adj[a2, q] = b2
            adj[b1, s1] = a1
            adj[b2, s2] = a2
    return best, best_adj


def _adj_edges(adj, nA):
    """Edge list of a bipartite neighbour array whose A side is 0..nA-1."""
    return [(a, int(b)) for a in range(nA) for b in adj[a].tolist()]


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


def _extend(n, edges, d, D, rng, deadline, max_fail=300):
    """Greedy pair insertion: repeatedly grow the order by 2 while the result stays valid."""
    if d < 1 or not edges:
        return n, edges
    color = _two_color(n, edges)
    if color is None:
        return n, edges
    edges = list(edges)
    color = list(color)
    fails = 0
    while time.monotonic() < deadline and fails < max_fail:
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
            fails = 0
        else:
            fails += 1
    return n, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.55 * budget
    repair_deadline = start + 0.8 * budget
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

    # Exact constructions: return immediately (calibration-style cases).
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

    # Main search with a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    near = []  # near-miss lifts: (cost, N, adj, nA)

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < search_deadline:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, search_deadline, 4000)
        if res is None:
            continue
        N, adj, unr = res
        if unr == 0:
            wins[k] += 1
            consider(N, _adj_edges(adj, k * G))
        elif N > best_n:
            near.append((unr, N, adj, k * G))
            near.sort(key=lambda c: (c[0], -c[1]))
            del near[5:]

    # NEW: 2-switch annealing repair on the most promising near-miss lift.
    near = [c for c in near if c[1] > best_n]
    for unr, N, adj, nA in near[:2]:
        if time.monotonic() > repair_deadline:
            break
        cost, fixed = _switch_repair(adj, nA, D, rng, repair_deadline)
        if cost == 0:
            consider(N, _adj_edges(fixed, nA))
            break

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
