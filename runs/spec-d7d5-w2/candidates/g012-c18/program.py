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
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (structured search).
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
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


# ----------------------------------------------------------------------------
# New search regime: general d-regular bipartite annealing (repair from a
# structured start). Sides: A = 0..h-1, B = h..2h-1. Edge arrays ea (A index),
# eb (B index). Degrees are always exactly d (edge swaps preserve them), and
# duplicate edges are penalised in the cost.
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


def _neighbours(h, ea, eb, d):
    """(2h, d) neighbour table. Assumes every vertex has degree exactly d."""
    N = 2 * h
    u = np.concatenate([ea, h + eb])
    w = np.concatenate([h + eb, ea])
    order = np.argsort(u, kind="stable")
    return w[order].reshape(N, d)


def _bad_pairs(N, nb, D):
    """Number of unordered vertex pairs at distance > D, via bitsets."""
    W = (N + 63) // 64
    reach = np.zeros((N, W), dtype=np.uint64)
    idx = np.arange(N, dtype=np.int64)
    reach[idx, idx >> 6] = np.left_shift(np.uint64(1), (idx & 63).astype(np.uint64))
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nb], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    total = int(_POP8[reach.view(np.uint8)].sum())
    return (N * N - total) // 2


def _anneal(h, ea, eb, d, D, rng, deadline, iters):
    """Edge-swap annealing on bad pairs + duplicate penalty. Mutates ea, eb. True if cost reached 0."""
    E = len(ea)
    cnt = np.zeros((h, h), dtype=np.int64)
    np.add.at(cnt, (ea, eb), 1)
    dup = int(np.maximum(cnt - 1, 0).sum())

    def bump(a, b, s):
        c = int(cnt[a, b])
        cnt[a, b] = c + s
        if s > 0:
            return 1 if c >= 1 else 0
        return -1 if c >= 2 else 0

    def cost_of(dp):
        nb = _neighbours(h, ea, eb, d)
        return _bad_pairs(2 * h, nb, D) + _PENALTY * dp

    cost = cost_of(dup)
    temp0 = 2.0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.05, temp0 * (1.0 - t / iters))
        i = rng.randrange(E)
        j = rng.randrange(E)
        a1, b1 = int(ea[i]), int(eb[i])
        a2, b2 = int(ea[j]), int(eb[j])
        if a1 == a2 or b1 == b2:
            continue
        delta = bump(a1, b1, -1) + bump(a2, b2, -1)
        delta += bump(a1, b2, 1) + bump(a2, b1, 1)
        ea[i], eb[i] = a2, b1
        ea[j], eb[j] = a1, b2
        new_cost = cost_of(dup + delta)
        if new_cost <= cost or rng.random() < math.exp(-(new_cost - cost) / temp):
            cost = new_cost
            dup += delta
        else:
            ea[i], eb[i] = a1, b1
            ea[j], eb[j] = a2, b2
            bump(a2, b1, -1)
            bump(a1, b2, -1)
            bump(a1, b1, 1)
            bump(a2, b2, 1)
    return cost == 0


def _insert_pair(h, ea, eb, d, rng):
    """Add two vertices x (A index h) and y (B index h), keeping d-regularity. Returns (h+1, ea, eb) or None."""
    E = len(ea)
    order = list(range(E))
    rng.shuffle(order)
    chosen = []
    ua, ub = set(), set()
    for t in order:
        if len(chosen) == d - 1:
            break
        a = int(ea[t])
        b = int(eb[t])
        if a in ua or b in ub:
            continue
        chosen.append(t)
        ua.add(a)
        ub.add(b)
    if len(chosen) < d - 1:
        return None
    ea2 = ea.copy()
    eb2 = eb.copy()
    new_a, new_b = [], []
    for t in chosen:
        new_b.append(int(eb[t]))   # edge (x, b_t)
        new_a.append(h)
        eb2[t] = h                  # edge (a_t, y)
    new_a.append(h)                 # edge (x, y)
    new_b.append(h)
    ea3 = np.concatenate([ea2, np.array(new_a, dtype=np.int64)])
    eb3 = np.concatenate([eb2, np.array(new_b, dtype=np.int64)])
    return h + 1, ea3, eb3


def _repair_grow(d, D, n0, edges0, rng, deadline, consider):
    """Grow a valid d-regular bipartite graph by pair insertion + annealing repair."""
    color = _two_color(n0, edges0)
    if color is None:
        return
    deg = [0] * n0
    for u, v in edges0:
        deg[u] += 1
        deg[v] += 1
    if any(x != d for x in deg):
        return
    A = [v for v in range(n0) if color[v] == 0]
    B = [v for v in range(n0) if color[v] == 1]
    if len(A) != len(B) or not A:
        return
    ia = {v: i for i, v in enumerate(A)}
    ib = {v: i for i, v in enumerate(B)}
    h = len(A)
    ea_l, eb_l = [], []
    for u, v in edges0:
        if color[u] == 0:
            ea_l.append(ia[u])
            eb_l.append(ib[v])
        else:
            ea_l.append(ia[v])
            eb_l.append(ib[u])
    ea = np.array(ea_l, dtype=np.int64)
    eb = np.array(eb_l, dtype=np.int64)

    while time.monotonic() < deadline:
        ins = _insert_pair(h, ea, eb, d, rng)
        if ins is None:
            break
        h2, ea2, eb2 = ins
        ok = _anneal(h2, ea2, eb2, d, D, rng, deadline, 2500)
        if ok:
            h, ea, eb = h2, ea2, eb2
            edges = [(a, h + b) for a, b in zip(ea.tolist(), eb.tolist())]
            consider(2 * h, edges)


# ----------------------------------------------------------------------------
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.90 * time_limit, time_limit - 5.0))
    deadline = start + budget
    search_deadline = start + 0.6 * budget
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
            best = (n, list(e))
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < search_deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: structured bi-Cayley search with a bandit over base sizes.
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

    # Phase 2 (new regime): grow the best regular graph by pair insertion
    # and repair each step with edge-swap annealing on bad pairs.
    if D >= 5 and best_n >= 4:
        try:
            _repair_grow(d, D, best[0], best[1], rng, deadline, consider)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
