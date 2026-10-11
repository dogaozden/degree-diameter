import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact or safe baseline families.
# ----------------------------------------------------------------------------

_PEN = 1000
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Group tables. Each group G has Ts[s, g] = g*s and Invs[s, h] = g with g*s = h.
# Two families: abelian Z_a x Z_b (non-cyclic when b > 1) and semidirect Z_m x| Z_k2.
# ----------------------------------------------------------------------------

def _abelian_tables(a, b):
    G = a * b
    x = np.arange(G, dtype=np.int64)
    gi, gj = x // b, x % b
    M = ((gi[:, None] + gi[None, :]) % a) * b + (gj[:, None] + gj[None, :]) % b  # M[g,s] = g*s
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _semidirect_tables(m, k2, r):
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


def _sample_group(target, rng):
    """Return a group descriptor with order at least target, or None."""
    if rng.random() < 0.5:
        b = rng.choice([2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12])
        a = max(2, -(-target // b))
        return ("ab", a, b)
    for _ in range(60):
        k2 = rng.choice([2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24])
        m = max(2, -(-target // k2))
        for _ in range(60):
            r = rng.randrange(2, m) if m > 2 else 1
            if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
                return ("sd", m, k2, r)
    return None


def _tables(g):
    if g[0] == "ab":
        return _abelian_tables(g[1], g[2])
    return _semidirect_tables(g[1], g[2], g[3])


# ----------------------------------------------------------------------------
# Bi-Cayley lift search: coordinate descent over voltages.
# A-block i joins B-block layers[l][i] in layer l with voltage S[l][i]:
#   A_{i,g} ~ B_{j,g*s}.  Every layer is a permutation, so every vertex has
# degree d. Repeated (i, j, s) triples would duplicate edges and are penalised.
# Each step rescans all voltages of one randomly chosen dart and keeps the best
# (sideways moves allowed). Stalls trigger a small random kick.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, stall_limit):
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def setd(l, i):
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def score():
        reach = _reach(k, G, D, nbr, d)
        unr = 2 * k * N - int(_POP[reach].sum())
        keys = {(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)}
        dup = d * k - len(keys)
        return unr + _PEN * dup

    cost = score()
    stall = 0
    while cost > 0:
        if time.monotonic() > deadline:
            return None

        if k >= 2 and rng.random() < 0.1:
            # Layer swap: exchange the B-targets of two A-blocks in one layer.
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            setd(l, i1)
            setd(l, i2)
            c2 = score()
            if c2 <= cost:
                improved = c2 < cost
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                setd(l, i1)
                setd(l, i2)
                improved = False
            stall = 0 if improved else stall + 1
            continue

        # Coordinate descent on one voltage: scan all G values.
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        best_c, best_list = None, []
        for s in range(G):
            if s == old:
                continue
            if time.monotonic() > deadline:
                break
            S[l][i] = s
            setd(l, i)
            c = score()
            if best_c is None or c < best_c:
                best_c, best_list = c, [s]
            elif c == best_c:
                best_list.append(s)
        if best_c is None:
            S[l][i] = old
            setd(l, i)
            continue
        if best_c <= cost or rng.random() < 0.02:
            S[l][i] = rng.choice(best_list)
        else:
            S[l][i] = old
        setd(l, i)
        c_new = score()
        if c_new < cost:
            stall = 0
        else:
            stall += 1
        cost = c_new

        if stall > stall_limit:
            for _ in range(2):
                l2 = rng.randrange(d)
                i2 = rng.randrange(k)
                S[l2][i2] = rng.randrange(G)
                setd(l2, i2)
            cost = score()
            stall = 0

    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            w = int(v)
            edges.add((u, w) if u < w else (w, u))
    if len(edges) != N * d // 2:
        return None
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Greedy pair insertion (grows the order by 2 per accepted step).
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


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.80 * budget
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

    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: lifts over non-cyclic groups with a coordinate-descent search.
    if d >= 3 and D >= 3:
        while time.monotonic() < search_deadline:
            k = rng.choice([2, 3, 4, 5, 6])
            Gt = best_n // (2 * k) + 1 + rng.randrange(0, 4)
            g = _sample_group(Gt, rng)
            if g is None:
                continue
            G, Ts, Invs = _tables(g)
            if 2 * k * G <= best_n or G > 400:
                continue
            res = _search(d, D, k, G, Ts, Invs, rng,
                          min(search_deadline, time.monotonic() + 12.0), 80)
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
