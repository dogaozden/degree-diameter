import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact and safe baselines.
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
# Group tables. Every family below is a voltage group: a base graph with k
# blocks per side, lifted over a finite group G. Left multiplication is an
# automorphism, so validity only needs BFS from the 2k block identities.
#
# New in this version: non-abelian simple-type groups PSL(2,p) and PGL(2,p),
# which the parent never tried. PGL(2,11) with k=1 gives a 2640-vertex graph.
# Semidirect products Z_m x| Z_k2 are kept as a second arm for safety.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4, 6, 8)
_LIN_GROUPS = [(5, False), (5, True), (7, False), (7, True),
               (11, False), (11, True), (13, False)]
_LIN_MAX_ORDER = 1400


def _tables_from_mul(M):
    """Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, from the multiplication table M[g, s] = g*s."""
    G = M.shape[0]
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G)[None, :], (G, G))
    return Ts, Invs


def _lin_order(p, proj):
    return p * (p * p - 1) if proj else p * (p * p - 1) // 2


def _linear_group(p, proj):
    """Return (G, Ts, Invs, ident) for PSL(2,p) (proj False) or PGL(2,p) (proj True), p prime."""
    K = p ** 4

    def dec(x):
        return (x // p ** 3, (x // p ** 2) % p, (x // p) % p, x % p)

    def enc(a, b, c, e):
        return ((a * p + b) * p + c) * p + e

    canon = np.full(K, -1, dtype=np.int64)
    for x in range(K):
        a, b, c, e = dec(x)
        det = (a * e - b * c) % p
        if proj:
            if det == 0:
                continue
            canon[x] = min(enc(lam * a % p, lam * b % p, lam * c % p, lam * e % p)
                           for lam in range(1, p))
        else:
            if det != 1:
                continue
            canon[x] = min(x, enc((-a) % p, (-b) % p, (-c) % p, (-e) % p))
    elems = np.unique(canon[canon >= 0])
    G = len(elems)
    idx = np.full(K, -1, dtype=np.int64)
    idx[elems] = np.arange(G)
    A = np.array([dec(int(x)) for x in elems], dtype=np.int64)
    a0, a1, a2, a3 = [A[:, t:t + 1] for t in range(4)]
    b0, b1, b2, b3 = [A[:, t].reshape(1, G) for t in range(4)]
    c00 = (a0 * b0 + a1 * b2) % p
    c01 = (a0 * b1 + a1 * b3) % p
    c10 = (a2 * b0 + a3 * b2) % p
    c11 = (a2 * b1 + a3 * b3) % p
    pk = ((c00 * p + c01) * p + c10) * p + c11
    M = idx[canon[pk]]
    ident = int(idx[canon[enc(1, 0, 0, 1)]])
    Ts, Invs = _tables_from_mul(M)
    return G, Ts, Invs, ident


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
    """Return (G, Ts, Invs, ident) for Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)."""
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts, Invs = _tables_from_mul(M)
    return G, Ts, Invs, 0


def _lin_arms(best_n, cap):
    """Group/block configurations whose vertex count 2*k*|G| beats best_n and is at most cap."""
    arms = []
    for p, proj in _LIN_GROUPS:
        order = _lin_order(p, proj)
        if order > _LIN_MAX_ORDER:
            continue
        for k in (1, 2, 3, 4, 6, 7, 8):
            n = 2 * k * order
            if best_n < n <= cap:
                arms.append(("lin", p, proj, k))
    return arms


# ----------------------------------------------------------------------------
# Simulated annealing over voltage assignments.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Layer l joins A_{i,g} to B_{j,g*s} for all g."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, ident, D, nbr, d):
    """Bitmask per vertex: bit b is set when block representative b is within distance D."""
    N = nbr.shape[1]
    reach = np.zeros(N, dtype=np.int64)
    for b in range(2 * k):
        reach[b * G + ident] = 1 << b
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


def _search(d, D, k, G, ident, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over the voltages and layer permutations. Returns (n, edges) or None."""
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

    reach = _reach(k, G, ident, D, nbr, d)
    cost = _unreached(k, N, reach) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))
    best_cost = cost
    last_improve = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last_improve > patience:
            break
        temp = max(0.3, 0.01 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.25:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            undo = (0, l, i1, i2)
        else:
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
            undo = (1, l, i, old)

        r2 = _reach(k, G, ident, D, nbr, d)
        c2 = _unreached(k, N, r2) + _PENALTY * dupcount()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last_improve = cost, t
        else:
            if undo[0] == 0:
                _, l, i1, i2 = undo
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            else:
                _, l, i, old = undo
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
# Driver.
# ----------------------------------------------------------------------------

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

    # Exact constructions, returned immediately for calibration-style cases.
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

    # Portfolio search: bandit over PSL/PGL(2,p) lifts and semidirect lifts.
    cap = lib.moore_bound(d, D)
    stats = {}
    cache = {}

    def pick(arms):
        if rng.random() < 0.2:
            return rng.choice(arms)
        return max(arms, key=lambda a: (stats.get(a, (0, 0))[0] + 1)
                   / (stats.get(a, (0, 0))[1] + 2) + 0.03 * rng.random())

    try:
        while time.monotonic() < deadline:
            arms = _lin_arms(best_n, cap) + [("sd", k) for k in _KS]
            arm = pick(arms)
            if arm[0] == "lin":
                _, p, proj, k = arm
                key = (p, proj)
                if key not in cache:
                    cache[key] = _linear_group(p, proj)
                G, Ts, Invs, ident = cache[key]
            else:
                k = arm[1]
                base = best_n // (2 * k)
                target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
                g = _sample_group(target, rng)
                if g is None:
                    continue
                G, Ts, Invs, ident = _semidirect_tables(*g)
            if 2 * k * G <= best_n:
                continue
            st = stats.get(arm, (0, 0))
            stats[arm] = (st[0], st[1] + 1)
            res = _search(d, D, k, G, ident, Ts, Invs, rng, deadline, 20000, 3000)
            if res is not None:
                st = stats[arm]
                stats[arm] = (st[0] + 1, st[1])
                consider(res[0], res[1])
    except Exception:
        pass  # keep whatever valid graph we already have

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
