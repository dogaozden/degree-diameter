import bisect
import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (safe, instant when they apply).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Generic group tables.
#
# A group is given by its multiplication table M (G x G, M[x, y] = x*y).
# Ts[s, g] = g*s and Invs[s, h] = g with g*s = h. Right multiplication gives
# bipartite graphs with left-multiplication automorphisms, so the block-reach
# test only needs one start per block.
#
# NEW FAMILY: non-abelian groups beyond semidirect Z_m x| Z_k:
#   * affine groups AGL(1,q) = {x -> a x + b} over GF(q) (Frobenius groups),
#   * their direct products with cyclic groups Z_c.
# These are combined with semidirect products and cyclic groups.
# ----------------------------------------------------------------------------

_MAX_ORDER = 1000
_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 5, 6)
_GF_CACHE = {}
_POOL = None


def _gf(q):
    if q not in _GF_CACHE:
        _GF_CACHE[q] = lib.GF(q)
    return _GF_CACHE[q]


def _tables_from_mul(M):
    G = M.shape[0]
    x = np.arange(G, dtype=np.int64)
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    Invs[np.arange(G)[:, None], Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _affine_mul(q):
    """AGL(1,q): elements (a, b), a != 0, as x -> a x + b; index (a-1)*q + b."""
    F = _gf(q)
    a = np.repeat(np.arange(1, q, dtype=np.int64), q)
    b = np.tile(np.arange(q, dtype=np.int64), q - 1)
    pa = F.mul_table[a[:, None], a[None, :]]
    pb = F.add_table[F.mul_table[a[:, None], b[None, :]], b[:, None]]
    return (pa - 1) * q + pb


def _times_cyclic(M, c):
    G = M.shape[0]
    x = np.arange(G * c, dtype=np.int64)
    ax, bx = x // c, x % c
    return M[ax[:, None], ax[None, :]] * c + (bx[:, None] + bx[None, :]) % c


def _semidirect_mul(m, k2, r):
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a, b = x // k2, x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    return ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2


def _pick_r(m, k2, rng):
    if k2 == 1:
        return 1 % m
    cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
    if not cands:
        return None
    return rng.choice(cands)


def _make_pool():
    pool = {"aff": [], "affz": [], "sd": [], "cyc": []}
    for q in range(3, 40):
        if lib.is_prime_power(q) and q * (q - 1) <= _MAX_ORDER:
            base = q * (q - 1)
            pool["aff"].append((base, ("aff", q)))
            for c in range(2, _MAX_ORDER // base + 1):
                pool["affz"].append((base * c, ("affz", q, c)))
    for m in range(3, _MAX_ORDER + 1):
        pool["cyc"].append((m, ("cyc", m)))
    for k2 in range(2, 13):
        for m in range(3, _MAX_ORDER // k2 + 1):
            pool["sd"].append((m * k2, ("sd", m, k2)))
    out = {}
    for kind, lst in pool.items():
        lst.sort()
        out[kind] = ([o for o, _ in lst], [s for _, s in lst])
    return out


def _build_group(spec, rng):
    kind = spec[0]
    if kind == "aff":
        M = _affine_mul(spec[1])
    elif kind == "affz":
        M = _times_cyclic(_affine_mul(spec[1]), spec[2])
    elif kind == "cyc":
        m = spec[1]
        x = np.arange(m, dtype=np.int64)
        M = (x[:, None] + x[None, :]) % m
    else:
        m, k2 = spec[1], spec[2]
        r = _pick_r(m, k2, rng)
        if r is None:
            return None
        M = _semidirect_mul(m, k2, r)
    return _tables_from_mul(M)


# ----------------------------------------------------------------------------
# Block-level simulated annealing over voltage assignments.
# ----------------------------------------------------------------------------

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


# ----------------------------------------------------------------------------
# Slack extension for non-regular graphs (safe, verified with lib.is_valid).
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


def _has_spare(n, edges, d):
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return sum(1 for x in deg if x < d) >= d


def _slack_extend(n, edges, d, D, rng, deadline):
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    global _POOL
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 5.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    if D >= 2 and d >= 2 and time.monotonic() < deadline:
        if _POOL is None:
            _POOL = _make_pool()
        trials = {k: 0 for k in _KS}
        wins = {k: 0 for k in _KS}
        kind_weights = (("aff", 0.3), ("affz", 0.3), ("sd", 0.3), ("cyc", 0.1))

        def pick_k():
            if rng.random() < 0.2:
                return rng.choice(_KS)
            return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

        def pick_kind():
            x = rng.random()
            acc = 0.0
            for kind, w in kind_weights:
                acc += w
                if x < acc:
                    return kind
            return "cyc"

        while time.monotonic() < deadline:
            k = pick_k()
            G_min = best_n // (2 * k) + 1
            if G_min > _MAX_ORDER:
                continue
            hi_bound = G_min + max(3, G_min // 8)

            kind = pick_kind()
            orders, specs = _POOL[kind]
            i0 = bisect.bisect_left(orders, G_min)
            i1 = bisect.bisect_right(orders, hi_bound)
            if i0 == i1:
                orders, specs = _POOL["cyc"]
                i0 = bisect.bisect_left(orders, G_min)
                i1 = bisect.bisect_right(orders, hi_bound)
                if i0 == i1:
                    continue
            spec = specs[rng.randrange(i0, i1)]
            grp = _build_group(spec, rng)
            if grp is None:
                continue
            G, Ts, Invs = grp
            if 2 * k * G <= best_n:
                continue
            trials[k] += 1
            res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000, 1200)
            if res is not None:
                wins[k] += 1
                consider(res[0], res[1])

    if time.monotonic() < final_deadline and _has_spare(best[0], best[1], d):
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
