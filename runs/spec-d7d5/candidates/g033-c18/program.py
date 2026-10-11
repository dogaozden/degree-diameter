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


def _araujo_for(d):
    """Araujo-Pardo & Lopez record graph for d = q + 2 with q a prime power (D = 3 only)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

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
# NEW ARM: bi-Cayley lifts over the affine-type groups F_q x| H, H <= F_q^*.
#
# Elements are pairs (a, b) acting as x -> a*x + b, with a in a cyclic subgroup
# H of F_q^*. Product: (a, b)(c, e) = (a c, a e + b). These groups are not
# metacyclic in general (the old arm only used Z_m x| Z_k), and orders such
# as 600 = 25*24, 588 = 49*12, 294 = 49*6, 300 = 25*12 fall in the useful range.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A-block i with B-block p[l][i] through voltage s = S[l][i]:
#   A_{i,g} ~ B_{p, g*s},   B_{j,h} ~ A_{i, h*s^{-1}}.
# Left multiplication is an automorphism, so reachability from the 2k block
# identities (element 0) covers all vertices. Each layer is a perfect matching
# of blocks, so every vertex has degree d.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_AFF_QMAX = 49
_AFF_GMAX = 1200
_GF_CACHE = {}
_GROUP_CACHE = {}


def _affine_specs():
    """List (q, h, G) for every F_q x| H with prime power q <= _AFF_QMAX and G <= _AFF_GMAX."""
    specs = []
    for q in range(4, _AFF_QMAX + 1):
        if not lib.is_prime_power(q):
            continue
        for h in range(2, q):
            if (q - 1) % h == 0 and q * h <= _AFF_GMAX:
                specs.append((q, h, q * h))
    return specs


def _affine_group(q, h):
    """Return (G, M, Inv): multiplication table M[x, y] = x*y and inverse table, identity = 0."""
    key = (q, h)
    if key in _GROUP_CACHE:
        return _GROUP_CACHE[key]
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    F = _GF_CACHE[q]
    gen = F.primitive_element()
    step = (q - 1) // h
    Ha = np.array([F.pow(gen, step * j) for j in range(h)], dtype=np.int64)  # Ha[0] = 1
    pos = np.full(q, -1, dtype=np.int64)
    pos[Ha] = np.arange(h, dtype=np.int64)
    MH = pos[F.mul_table[Ha[:, None], Ha[None, :]]]
    G = q * h
    X = np.arange(G, dtype=np.int64)
    Xa, Xb = X // q, X % q
    prod_a = MH[Xa[:, None], Xa[None, :]]
    ae = F.mul_table[Ha[Xa][:, None], Xb[None, :]]
    prod_b = F.add_table[ae, Xb[:, None]]
    M = (prod_a * q + prod_b).astype(np.int64)
    Inv = np.empty(G, dtype=np.int64)
    idx = np.argwhere(M == 0)
    Inv[idx[:, 0]] = idx[:, 1]
    if len(_GROUP_CACHE) > 6:
        _GROUP_CACHE.clear()
    _GROUP_CACHE[key] = (G, M, Inv)
    return G, M, Inv


def _affine_search(d, D, k, G, M, Inv, rng, deadline, iters, patience):
    """Simulated annealing over layer permutations and voltages. Returns (n, edges) or None."""
    N = 2 * k * G
    nbr = np.empty((d, N), dtype=np.int64)
    p = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]

    def set_layer(l):
        for i in range(k):
            j = p[l][i]
            s = S[l][i]
            nbr[l, i * G:(i + 1) * G] = (k + j) * G + M[:, s]
            nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + M[:, Inv[s]]

    for l in range(d):
        set_layer(l)

    def dups():
        tot = 0
        for i in range(k):
            tot += d - len({(p[l][i], S[l][i]) for l in range(d)})
        return tot

    def evaluate():
        reach = np.zeros((2 * k, N), dtype=bool)
        for b in range(2 * k):
            reach[b, b * G] = True
        for _ in range(D):
            new = reach.copy()
            for l in range(d):
                new |= reach[:, nbr[l]]
            if np.array_equal(new, reach):
                break
            reach = new
        return 2 * k * N - int(reach.sum())

    cost = evaluate() + _PENALTY * dups()
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)
        old_p, old_s = list(p[l]), list(S[l])
        if k >= 2 and rng.random() < 0.3:
            i1, i2 = rng.sample(range(k), 2)
            p[l][i1], p[l][i2] = p[l][i2], p[l][i1]
        else:
            i = rng.randrange(k)
            S[l][i] = rng.randrange(G)
        set_layer(l)
        c2 = evaluate() + _PENALTY * dups()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            p[l], S[l] = old_p, old_s
            set_layer(l)

    if cost != 0:
        return None
    edges = set()
    for v in range(N):
        for l in range(d):
            w = int(nbr[l, v])
            edges.add((min(v, w), max(v, w)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# OLD ARM: bi-Cayley lifts over semidirect products Z_m x| Z_k2 (parent code).
# ----------------------------------------------------------------------------

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
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
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
                if cost < best_cost:
                    best_cost, last_improve = cost, t
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
            if cost < best_cost:
                best_cost, last_improve = cost, t
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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
        if D == 3:
            ar = _araujo_for(d)
            if ar is not None:
                consider(ar[0], ar[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    specs = _affine_specs()

    def affine_trial():
        """New arm: bi-Cayley lift over F_q x| H. Returns False if no group fits the size window."""
        k = rng.choice((1, 1, 2, 2, 3))
        cands = [s for s in specs if best_n < 2 * k * s[2] <= 1.8 * best_n + 40]
        if not cands:
            return False
        cands.sort(key=lambda s: s[2])
        q, h, _ = cands[int(len(cands) * rng.random() ** 2)]
        G, M, Inv = _affine_group(q, h)
        res = _affine_search(d, D, k, G, M, Inv, rng, deadline, 6000, 1500)
        if res is not None:
            consider(res[0], res[1])
        return True

    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    def semidirect_trial():
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            return False
        m, k2, r = g
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            return False
        trials[k] += 1
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
        return True

    while time.monotonic() < deadline:
        if rng.random() < 0.7:
            if not affine_trial():
                semidirect_trial()
        else:
            semidirect_trial()

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
