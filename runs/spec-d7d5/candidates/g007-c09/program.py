import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact families (used for D = 3 and D = 4).
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
# Bold new family for D >= 5: random d-regular bipartite graphs repaired by
# double-edge switches. Cost = number of unordered vertex pairs at distance > D,
# evaluated with bit-packed reachability in numpy.
# ----------------------------------------------------------------------------

_POP8 = np.array([bin(x).count("1") for x in range(256)], dtype=np.int64)


def _rr_init(h, d, rng):
    """Union of d random perfect matchings between A = 0..h-1 and B = h..2h-1, simple by construction."""
    E = set()
    nbr = np.empty((2 * h, d), dtype=np.int64)
    for l in range(d):
        while True:
            p = list(range(h))
            rng.shuffle(p)
            ok = True
            for i in range(h):
                if (i, p[i]) not in E:
                    continue
                fixed = False
                for _ in range(300):
                    j = rng.randrange(h)
                    if j == i:
                        continue
                    if (i, p[j]) not in E and (j, p[i]) not in E:
                        p[i], p[j] = p[j], p[i]
                        fixed = True
                        break
                if not fixed:
                    ok = False
                    break
            if ok:
                break
        for i in range(h):
            E.add((i, p[i]))
            nbr[i, l] = h + p[i]
            nbr[h + p[i], l] = i
    return nbr


def _rr_bad(nbr, n, D):
    """Number of unordered vertex pairs at distance > D (bit-packed reachability)."""
    W = (n + 63) // 64
    reach = np.zeros((n, W), dtype=np.uint64)
    idx = np.arange(n)
    reach[idx, idx // 64] = np.uint64(1) << (idx % 64).astype(np.uint64)
    for _ in range(D):
        new = reach | np.bitwise_or.reduce(reach[nbr], axis=1)
        if np.array_equal(new, reach):
            break
        reach = new
    pc = int(_POP8[reach.view(np.uint8)].sum())
    return (n * n - pc) // 2


def _rr_move(nbr, h, d, rng):
    """Propose a double-edge switch keeping the graph simple and bipartite (or None)."""
    a1 = rng.randrange(h)
    a2 = rng.randrange(h)
    if a1 == a2:
        return None
    s = rng.randrange(d)
    t = rng.randrange(d)
    b1 = int(nbr[a1, s])
    b2 = int(nbr[a2, t])
    if b1 == b2:
        return None
    if (nbr[a1] == b2).any() or (nbr[a2] == b1).any():
        return None
    u = int(np.argmax(nbr[b1] == a1))
    w = int(np.argmax(nbr[b2] == a2))
    return (a1, s, a2, t, b1, u, b2, w)


def _rr_apply(nbr, mv):
    a1, s, a2, t, b1, u, b2, w = mv
    nbr[a1, s] = b2
    nbr[a2, t] = b1
    nbr[b1, u] = a2
    nbr[b2, w] = a1


def _rr_undo(nbr, mv):
    a1, s, a2, t, b1, u, b2, w = mv
    nbr[a1, s] = b1
    nbr[a2, t] = b2
    nbr[b1, u] = a1
    nbr[b2, w] = a2


def _rr_edges(nbr, h):
    d = nbr.shape[1]
    return [(i, int(nbr[i, l])) for i in range(h) for l in range(d)]


def _rr_search(h, d, D, rng, deadline):
    """Simulated annealing over switches. Returns (best_cost, best_nbr)."""
    n = 2 * h
    nbr = _rr_init(h, d, rng)
    cost = _rr_bad(nbr, n, D)
    best_cost, best = cost, nbr.copy()
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cost > 0 and time.monotonic() < deadline:
        mv = _rr_move(nbr, h, d, rng)
        if mv is None:
            continue
        _rr_apply(nbr, mv)
        c2 = _rr_bad(nbr, n, D)
        frac = (time.monotonic() - t0) / span
        temp = max(0.2, 1.5 * (1.0 - frac))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_cost:
                best_cost, best = cost, nbr.copy()
        else:
            _rr_undo(nbr, mv)
    return best_cost, best


def _rr_ladder(d, D, h, hmax, rng, deadline):
    """Increase the side size h while the repair search still reaches zero bad pairs."""
    found = None
    while h <= hmax and time.monotonic() < deadline - 1.0:
        cap = min(deadline, time.monotonic() + 15.0)
        c, nbr = _rr_search(h, d, D, rng, cap)
        if c > 0:
            break
        found = (2 * h, _rr_edges(nbr, h))
        h += max(2, h // 150)
    return found


# ----------------------------------------------------------------------------
# Parent fallback: bi-Cayley lifts over semidirect products Z_m x| Z_k2.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
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
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b)."""
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


def _structured_init(d, k, G, Ts, rng):
    x = rng.randrange(1, G)
    powers = [0]
    for _ in range(d):
        powers.append(int(Ts[x, powers[-1]]))
    ys = [rng.randrange(G) for _ in range(k)]
    layers = [[(i + l) % k for i in range(k)] for l in range(d)]
    S = [[int(Ts[ys[i], powers[l + 1]]) for i in range(k)] for l in range(d)]
    return layers, S


def _random_init(d, k, G, rng):
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    return layers, S


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _bc_cost(k, G, D, nbr):
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    N = 2 * k * G
    if rng.random() < _STRUCT_PROB:
        layers, S = _structured_init(d, k, G, Ts, rng)
    else:
        layers, S = _random_init(d, k, G, rng)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _bc_cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        l = rng.randrange(d)

        if k > 1 and rng.random() < _SWAP_PROB:
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            c2 = _bc_cost(k, G, D, nbr) + _PENALTY * dupcount()
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost = c2
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _bc_cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
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


_PENALTY = 1000
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3
_STRUCT_PROB = 0.5


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Exact constructions.
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

    # Bold phase: random regular bipartite graphs repaired by switches.
    if D >= 5 and d >= 3:
        rr_deadline = start + 0.6 * budget
        hmax = lib._moore_bound(d, D) // 2
        h0 = max(best_n // 2 + 1, d + 1)
        found = _rr_ladder(d, D, h0, hmax, rng, rr_deadline)
        if found is not None:
            consider(found[0], found[1])

    # Parent fallback search for the remaining time.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
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
        res = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
