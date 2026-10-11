import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or near-exact constructions (instant returns for calibration-style cases).
# ----------------------------------------------------------------------------

_PENALTY = 1000
_KS = (1, 2, 3, 4)
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables. Every group here is a semidirect product Z_m x|_r Z_k2 with
# element a*k2+b and (a,b)(c,e) = (a + r^b c, b + e). r = 1 gives the abelian
# direct product Z_m x Z_k2, so this one family covers cyclic, abelian and
# non-abelian groups.
# ----------------------------------------------------------------------------

def _divisors(n):
    out = []
    i = 1
    while i * i <= n:
        if n % i == 0:
            out.append(i)
            if i * i != n:
                out.append(n // i)
        i += 1
    return out


def _group_candidates(G, rng, limit):
    """Random sample of (m, k2, r) with m*k2 = G, r^k2 = 1 mod m, gcd(r, m) = 1."""
    cands = []
    for k2 in _divisors(G):
        m = G // k2
        if m < 2:
            continue
        rs = [1]
        if k2 >= 2:
            pool = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            rng.shuffle(pool)
            rs += pool[:2]
        for r in rs:
            cands.append((m, k2, r))
    rng.shuffle(cands)
    return cands[:limit]


def _semidirect_table(m, k2, r):
    """Multiplication table M[g, h] of Z_m x|_r Z_k2 (element a*k2+b)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    return ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2


def _lift_tables(M):
    """Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    G = M.shape[0]
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G, dtype=np.int64)[None, :], (G, G))
    return Ts, Invs


# ----------------------------------------------------------------------------
# Bi-Cayley lifts: A_{i,g} ~ B_{j,g*s} for each layer l with dart (i -> j, s).
# Each layer is a permutation of the k A-blocks onto the k B-blocks, so every
# vertex has degree exactly d. Left multiplication is an automorphism, so the
# diameter check only needs distances from each vertex to the 2k block
# representatives.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative of block b is within distance D."""
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over layers and voltages. Returns (n, edges) or None."""
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
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last_improve = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        # Voltage move: defect-targeted with probability 0.4, otherwise uniform.
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
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u].tolist():
            edges.add((u, v))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree. Adding w joined to a set
# P of spare same-side vertices never lengthens old distances, and w reaches x
# within D iff some v in P is within D-1 of x. Checked with radius balls.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
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


def _radius_balls(n, adj, radius):
    reach = [1 << v for v in range(n)]
    for _ in range(radius):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return reach


def _slack_extend(n, edges, d, D, rng, deadline):
    edges = [tuple(e) for e in edges]
    adj = [list(a) for a in lib.adjacency(n, edges)]
    color = _bipartition(n, adj)
    if color is None or D < 2:
        return n, edges
    deg = [len(a) for a in adj]
    radius = D - 1

    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        ball = _radius_balls(n, adj, radius)
        full = (1 << n) - 1
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            accepted = False
            for _ in range(4000):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cover = 0
                for v in pick:
                    cover |= ball[v]
                if cover != full:
                    continue
                w = n
                edges.extend((v, w) for v in pick)
                adj.append(list(pick))
                for v in pick:
                    adj[v].append(w)
                    deg[v] += 1
                n += 1
                color.append(1 - side)
                deg.append(d)
                spare = [v for v in spare if deg[v] < d]
                grew = True
                accepted = True
                ball = _radius_balls(n, adj, radius)
                full = (1 << n) - 1
            if accepted:
                grew = True
    return n, edges


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(1.0, time_limit - 9.0)
    final_deadline = start + max(1.5, time_limit - 4.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, e

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best_n, best_e

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best_n, best_e

    # Main search: bi-Cayley lifts over a broad family of groups, aiming just
    # above the current best order for each base size k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        G_min = best_n // (2 * k) + 1
        G = G_min + rng.randrange(0, 11)
        cands = _group_candidates(G, rng, 4)
        if not cands:
            continue
        m, k2, r = rng.choice(cands)
        G = m * k2
        if 2 * k * G <= best_n:
            continue
        M = _semidirect_table(m, k2, r)
        Ts, Invs = _lift_tables(M)
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 3000, 900)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best_n, best_e, d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, best_e
