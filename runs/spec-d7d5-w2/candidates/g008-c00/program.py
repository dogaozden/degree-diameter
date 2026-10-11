import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families (parent program, unchanged).
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


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
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
                r = None
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
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


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
    """Simulated annealing over voltages, layer swaps and defect-targeted moves. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    reach = _reach(k, G, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

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
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
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
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


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
    """Greedy pair insertion: repeatedly grow the order by 2 while the result stays valid."""
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
        else:
            continue
    return n, edges


def _legacy_build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    search_deadline = start + 0.8 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

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
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    try:
        n2, e2 = _extend(best_n, best[1], d, D, rng, deadline)
        if n2 > best_n:
            consider(n2, e2)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best


# ----------------------------------------------------------------------------
# NEW (bold): Haar graphs over non-abelian groups PSL(2,p) x Z_k.
#
# Haar graph H(G, S): vertices A_g = g and B_h = N + h, with A_g ~ B_{g s} for s in S.
# Left multiplication by G is an automorphism, so the graph is vertex-transitive on
# each side. Diameter <= D therefore only needs a BFS from A_e and from B_e.
# |S| = d gives an exactly d-regular bipartite graph on 2N vertices. A random search
# over the d-set S (simulated annealing on unreached counts) is cheap, and any
# success is checked with lib.is_valid.
# ----------------------------------------------------------------------------

# (p, k) gives group PSL(2,p) x Z_k of order N = p(p^2-1)/2 * k, sorted ascending.
_TARGET_CANDS = [(5, 10), (11, 1), (7, 4), (5, 12), (7, 5), (7, 6), (13, 1), (7, 7)]


def _psl2_table(p):
    """Multiplication table (N x N int64) and order N of PSL(2,p), p prime >= 5."""
    codes = {}
    elems = []
    for a, b, c, e in itertools.product(range(p), repeat=4):
        if (a * e - b * c) % p != 1:
            continue
        c1 = ((a * p + b) * p + c) * p + e
        c2 = (((-a) % p * p + (-b) % p) * p + (-c) % p) * p + (-e) % p
        canon = min(c1, c2)
        if canon not in codes:
            codes[canon] = len(elems)
            elems.append(canon)
    N = len(elems)
    E = np.array(elems, dtype=np.int64)
    A = np.stack([E // p ** 3, (E // p ** 2) % p, (E // p) % p, E % p], axis=1)
    lut = np.full(p ** 4, -1, dtype=np.int64)
    lut[E] = np.arange(N, dtype=np.int64)
    a, b, c, e = A[:, 0], A[:, 1], A[:, 2], A[:, 3]
    T = np.empty((N, N), dtype=np.int64)
    for i in range(N):
        ai, bi, ci, di = [int(v) for v in A[i]]
        ra = (ai * a + bi * c) % p
        rb = (ai * b + bi * e) % p
        rc = (ci * a + di * c) % p
        rd = (ci * b + di * e) % p
        c1 = ((ra * p + rb) * p + rc) * p + rd
        c2 = (((-ra) % p * p + (-rb) % p) * p + (-rc) % p) * p + (-rd) % p
        T[i] = lut[np.minimum(c1, c2)]
    return T, N


def _times_cyclic(T0, k):
    """Table of the direct product G x Z_k, element (g, z) coded as g*k + z."""
    N0 = T0.shape[0]
    N = N0 * k
    I = np.arange(N, dtype=np.int64)
    g = I // k
    z = I % k
    T = T0[g[:, None], g[None, :]] * k + (z[:, None] + z[None, :]) % k
    return T, N


def _hs_cost(T, invT, ident, N, S, d, D):
    """Number of (source, vertex) pairs unreached within D, for sources A_e and B_e."""
    N2 = 2 * N
    invS = invT[S]
    adj = np.empty((N2, d), dtype=np.int64)
    adj[:N] = N + T[:, S]      # A_g ~ B_{g s}
    adj[N:] = T[:, invS]       # B_h ~ A_{h s^-1}
    total = 0
    for src in (ident, N + ident):
        vis = np.zeros(N2, dtype=bool)
        vis[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nb = adj[frontier].ravel()
            nb = np.unique(nb[~vis[nb]])
            if nb.size == 0:
                break
            vis[nb] = True
            frontier = nb
        total += N2 - int(vis.sum())
    return total


def _hs_search(T, invT, ident, N, d, D, rng, deadline):
    """Annealing with restarts over d-subsets S of G. Returns an array S with diameter <= D, or None."""
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        c = _hs_cost(T, invT, ident, N, np.array(S, dtype=np.int64), d, D)
        best_c = c
        stall = 0
        temp = 2.0
        while c > 0 and stall < 3000 and time.monotonic() < deadline:
            i = rng.randrange(d)
            new = rng.randrange(N)
            if new in S:
                continue
            S2 = list(S)
            S2[i] = new
            c2 = _hs_cost(T, invT, ident, N, np.array(S2, dtype=np.int64), d, D)
            if c2 <= c or rng.random() < math.exp(-(c2 - c) / temp):
                S, c = S2, c2
            if c < best_c:
                best_c = c
                stall = 0
            else:
                stall += 1
            temp = max(0.5, temp * 0.999)
        if c == 0:
            return np.array(S, dtype=np.int64)
    return None


def _target_build(d, D, seed, time_limit):
    """Haar graphs over PSL(2,p) x Z_k; returns a valid (n, edges) or None."""
    start = time.monotonic()
    deadline = start + max(1.0, min(0.85 * time_limit, time_limit - 8.0))
    rng = random.Random(seed)
    best, best_n = None, 0
    for p, k in _TARGET_CANDS:
        now = time.monotonic()
        remaining = deadline - now
        if remaining < 2.0:
            break
        T0, N0 = _psl2_table(p)
        T, N = _times_cyclic(T0, k) if k > 1 else (T0, N0)
        if 2 * N <= best_n:
            continue
        ident = int(np.flatnonzero(np.diag(T) == np.arange(N))[0])
        invT = np.argmax(T == ident, axis=1).astype(np.int64)
        slice_end = now + (0.35 * remaining if best is None else 0.5 * remaining)
        S = _hs_search(T, invT, ident, N, d, D, rng, slice_end)
        if S is None:
            continue
        us = np.repeat(np.arange(N, dtype=np.int64), d)
        vs = (N + T[:, S]).ravel()
        edges = list(zip(us.tolist(), vs.tolist()))
        n = 2 * N
        if lib.is_valid(n, edges, d, D):
            best, best_n = (n, edges), n
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    if d == 7 and D == 5:
        try:
            res = _target_build(d, D, seed, time_limit)
        except Exception:
            res = None
        if res is not None:
            return res
        remaining = time_limit - (time.monotonic() - start)
        return _legacy_build(d, D, seed, max(2.0, remaining))
    return _legacy_build(d, D, seed, time_limit)
