import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact constructions (returned immediately when they are optimal).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 40)."""
    for q in range(min(d - 1, 40), 1, -1):
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Number theory helpers.
# ----------------------------------------------------------------------------

def _is_prime(p):
    if p < 2:
        return False
    i = 2
    while i * i <= p:
        if p % i == 0:
            return False
        i += 1
    return True


def _primitive_root(p):
    phi = p - 1
    factors = []
    x = phi
    f = 2
    while f * f <= x:
        if x % f == 0:
            factors.append(f)
            while x % f == 0:
                x //= f
        f += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, phi // q, p) != 1 for q in factors):
            return g
    return 1


# ----------------------------------------------------------------------------
# Group families. Each returns (G, Ts) with Ts[s, g] = g * s and identity at 0.
# ----------------------------------------------------------------------------

def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    pos = np.full(p, -1, dtype=np.int64)
    for i, v in enumerate(H):
        pos[v] = i
    G = p * t
    idx = np.arange(G, dtype=np.int64)
    Hv = np.array(H, dtype=np.int64)
    A = Hv[idx // p]
    B = idx % p
    Ts = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        Ts[s] = pos[na] * p + nb
    return G, Ts


def _semidirect_table(m, k2, r):
    """Z_m x|_r Z_k2 with (a,b)(c,e) = (a + r^b c, b + e); element a*k2+b."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)
    return G, Ts


def _invert(G, Ts):
    """Invs[s, h] = the g with g*s = h."""
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G, dtype=np.int64)[None, :], (G, G))
    return Invs


def _sample_affine(target, rng):
    """Return (p, t) for the affine group of order p*t >= target, or None."""
    ts = list(range(1, 13))
    rng.shuffle(ts)
    for t in ts[:6]:
        p0 = max(3, -(-target // t))
        start = p0 + rng.randrange(0, 30)
        for p in range(start, start + 300):
            if p * t > 1500:
                break
            if (p - 1) % t == 0 and _is_prime(p):
                return p, t
    return None


def _sample_semi(target, rng):
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
        if m * k2 > 1500:
            continue
        return m, k2, r
    return None


def _sample_group(target, rng):
    """Return a group tables triple (G, Ts, Invs) of order >= target, or None."""
    if rng.random() < 0.5:
        aff = _sample_affine(target, rng)
        if aff is not None:
            p, t = aff
            G, Ts = _affine_table(p, t)
            return G, Ts, _invert(G, Ts)
    sm = _sample_semi(target, rng)
    if sm is None:
        return None
    m, k2, r = sm
    G, Ts = _semidirect_table(m, k2, r)
    return G, Ts, _invert(G, Ts)


# ----------------------------------------------------------------------------
# Bi-Cayley lifts with k base vertices per side.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_SWAP_PROB = 0.3


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-vertex base i (target B-base j) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs over all 2k representatives."""
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


def _nbr_edges(nbr, nA):
    """Edge list from layer neighbours; A-side vertices are 0..nA-1 and each edge is listed once."""
    edges = set()
    for u in range(nA):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return sorted(edges)


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer target swaps.

    Returns (cost, N, nbr). cost == 0 means the representative check passed;
    otherwise nbr is the final (possibly near-valid) state, used for repair.
    """
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
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
            c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
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
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    return cost, N, nbr.copy()


# ----------------------------------------------------------------------------
# NEW: delete-and-regrow repair.
#
# Starting from a near-valid graph with more vertices than the incumbent, repeatedly
# delete the vertex that sees the most unreached vertices, until the diameter is
# within D. Then regrow: add new vertices on one side, each joined to up to d
# deficient vertices of the other side, keeping a new vertex only if the whole
# graph stays within diameter D. Bipartiteness is kept by construction.
# ----------------------------------------------------------------------------

def _unreached(vs, adj, D):
    """For each vertex in vs (list), the number of alive vertices it cannot reach within D."""
    idx = {v: i for i, v in enumerate(vs)}
    m = len(vs)
    nb = [[idx[u] for u in adj[v]] for v in vs]
    reach = [1 << i for i in range(m)]
    for _ in range(D):
        new = []
        for i in range(m):
            r = reach[i]
            for j in nb[i]:
                r |= reach[j]
            new.append(r)
        if new == reach:
            break
        reach = new
    return [m - r.bit_count() for r in reach]


def _repair_regrow(n, edges, d, D, deadline, rng):
    """Return (n', edges') with diameter <= D, or None. Vertices are relabelled 0..n'-1."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)

    side = [-1] * n
    for s0 in range(n):
        if side[s0] != -1:
            continue
        side[s0] = 0
        stack = [s0]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if side[v] == -1:
                    side[v] = 1 - side[u]
                    stack.append(v)

    alive = set(range(n))

    # Phase 1: delete the worst vertices until no pair is too far apart.
    max_del = max(8, n // 4)
    dels = 0
    while True:
        if time.monotonic() > deadline or dels > max_del:
            return None
        vs = sorted(alive)
        un = _unreached(vs, adj, D)
        if sum(un) == 0:
            break
        mx = max(un)
        cands = [vs[i] for i, c in enumerate(un) if c == mx]
        v = rng.choice(cands)
        for u in adj[v]:
            adj[u].discard(v)
        adj[v] = set()
        alive.discard(v)
        dels += 1

    # Phase 2: regrow new vertices onto deficient vertices, keeping the diameter bound.
    fails = 0
    while fails < 30 and time.monotonic() < deadline:
        s = rng.randrange(2)
        pool = [v for v in alive if side[v] != s and len(adj[v]) < d]
        if not pool:
            fails += 1
            continue
        rng.shuffle(pool)
        nbrs = pool[:min(d, len(pool))]
        x = len(adj)
        adj.append(set())
        side.append(s)
        for u in nbrs:
            adj[x].add(u)
            adj[u].add(x)
        alive.add(x)
        if sum(_unreached(sorted(alive), adj, D)) == 0:
            fails = 0
        else:
            for u in nbrs:
                adj[u].discard(x)
            adj.pop()
            side.pop()
            alive.discard(x)
            fails += 1

    vs = sorted(alive)
    new = {v: i for i, v in enumerate(vs)}
    out = set()
    for v in vs:
        for u in adj[v]:
            a, b = new[v], new[u]
            out.add((min(a, b), max(a, b)))
    return len(vs), sorted(out)


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

    # Main search: bandit over base sizes k, affine and semidirect groups.
    ks = _KS
    trials = {k: 0 for k in ks}
    wins = {k: 0 for k in ks}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(ks)
        return max(ks, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while time.monotonic() < deadline:
        k = pick_k()
        base = best_n // (2 * k)
        if rng.random() < 0.25:
            target = base + base // 10 + 1 + rng.randrange(0, max(2, base // 10 + 1))
        else:
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        G, Ts, Invs = g
        if 2 * k * G <= best_n:
            continue
        trials[k] += 1
        before = best_n
        cost, N, nbr = _search(d, D, k, G, Ts, Invs, rng, deadline, 4000)
        if cost == 0:
            consider(N, _nbr_edges(nbr, k * G))
        elif N > best_n and cost <= max(6, N // 60) and time.monotonic() < deadline:
            # Near-valid and larger than the incumbent: try delete-and-regrow repair.
            rep_deadline = min(deadline, time.monotonic() + 4.0)
            r = _repair_regrow(N, _nbr_edges(nbr, k * G), d, D, rep_deadline, rng)
            if r is not None:
                consider(r[0], r[1])
        if best_n > before:
            wins[k] += 1

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
