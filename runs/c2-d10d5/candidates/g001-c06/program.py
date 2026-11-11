"""Bold variant for the weak d=10, D=5 target.

Change: the parent searched only over semidirect products Z_m x| Z_k2. This version
adds a different group family, the affine group AGL(1,q) = {x -> a x + b} over GF(q),
which is non-abelian and has orders q(q-1) (for example 342 for q=19, 272 for q=17,
156 for q=13). Bi-regular lifts over these groups are searched with the same exact
block-reachability annealing. Semidirect products are kept as a minority option.

Safety: every candidate is validated with lib.is_valid before it is returned, and the
fallback K_{d,d} (diameter 2) is always available. Exact constructions (PG(2,q) and
W(q)) are still used where they apply.
"""
import itertools
import math
import random
import time

import numpy as np

import lib


_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_KS = (1, 2, 3, 4)
_KMAX = 16
_AFF_QS = [q for q in range(7, 33) if lib.is_prime_power(q)]
_AFF_CACHE = {}


# ----------------------------------------------------------------------------
# Exact baseline families.
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
# Group tables. Every group G is given as Ts[s, g] = g*s (right multiplication)
# and Invs[s, h] = g with g*s = h.
# ----------------------------------------------------------------------------

def _affine_tables(q):
    """Tables for AGL(1,q). Element (a,b), a != 0, is the map x -> a x + b, coded as (a-1)*q + b.

    (a1,b1)(a2,b2) = (a1 a2, a1 b2 + b1).
    """
    cached = _AFF_CACHE.get(q)
    if cached is not None:
        return cached
    F = lib.GF(q)
    G = q * (q - 1)
    idx = np.arange(G, dtype=np.int64)
    A = idx // q + 1
    B = idx % q
    a1, a2 = A[:, None], A[None, :]
    b1, b2 = B[:, None], B[None, :]
    newa = F.mul_table[a1, a2]
    newb = F.add_table[F.mul_table[a1, b2], b1]
    M = (newa - 1) * q + newb
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(idx[None, :], (G, G))
    _AFF_CACHE[q] = (G, Ts, Invs)
    return _AFF_CACHE[q]


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
    """Tables for Z_m x| Z_k2 with element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e)."""
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


def _pick_affine(target, rng):
    """Pick (k, G, Ts, Invs) for an AGL(1,q) lift with 2kG >= target, preferring sizes near target."""
    cands = []
    for q in _AFF_QS:
        G = q * (q - 1)
        for k in range(1, _KMAX + 1):
            N = 2 * k * G
            if N >= target:
                cands.append((N, q, k))
    if not cands:
        return None
    cands.sort()
    window = [c for c in cands if c[0] <= 1.12 * target]
    pool = window if window else cands[:6]
    _, q, k = rng.choice(pool)
    G, Ts, Invs = _affine_tables(q)
    return k, G, Ts, Invs


def _pick_semidirect(target, rng):
    """Pick (k, G, Ts, Invs) for a semidirect-product lift with 2kG >= target."""
    k = rng.choice(_KS)
    g = _sample_group(target // (2 * k) + 1, rng)
    if g is None:
        return None
    m, k2, r = g
    G, Ts, Invs = _semidirect_tables(m, k2, r)
    return k, G, Ts, Invs


# ----------------------------------------------------------------------------
# Lift search. Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Left multiplication is an automorphism, so checking reachability from one
# representative per block is exact.
# ----------------------------------------------------------------------------

def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
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
    pc = _POP[reach & 0xFFFF] + _POP[(reach >> 16) & 0xFFFF]
    return 2 * k * N - int(pc.sum())


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing with stagnation restarts. Returns (n, edges) or None."""
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
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Slack extension (unchanged): add vertices using spare degree, validated.
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


def _largest_valid(cands, d, D):
    """Return the largest candidate that passes lib.is_valid, else K_{d,d}."""
    for n, e in sorted(cands, key=lambda c: -c[0]):
        if n > 0 and lib.is_valid(n, e, d, D):
            return n, e
    return lib.haar_graph(d, range(d))


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

    # Safe fallback: K_{d,d} has diameter 2.
    fallback = lib.haar_graph(d, range(d))
    cands = [fallback]

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            if D == 3 and lib.is_prime_power(d - 1) and lib.is_valid(pg[0], pg[1], d, D):
                return pg
            cands.append(pg)

    if D == 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            if d - 1 <= 9 and lib.is_prime_power(d - 1) and lib.is_valid(gq[0], gq[1], d, D):
                return gq
            cands.append(gq)

    # Main search: new AGL(1,q) lifts mostly, semidirect lifts as a minority.
    best_n = max(c[0] for c in cands)
    while time.monotonic() < deadline:
        target = int(best_n * (1.01 + 0.08 * rng.random())) + 1
        if target <= best_n:
            target = best_n + 1
        if rng.random() < 0.75:
            pick = _pick_affine(target, rng)
        else:
            pick = _pick_semidirect(target, rng)
        if pick is None:
            continue
        k, G, Ts, Invs = pick
        if 2 * k * G <= best_n:
            continue
        cap = min(deadline, time.monotonic() + 6.0)
        res = _search(d, D, k, G, Ts, Invs, rng, cap, 4000, 1200)
        if res is not None:
            cands.append(res)
            best_n = max(best_n, res[0])

    result = _largest_valid(cands, d, D)

    # Use any spare degree in the result to add vertices (cheap; often a no-op).
    if time.monotonic() < final_deadline - 1.0 and result[0] > 0:
        n2, e2 = _slack_extend(result[0], result[1], d, D, rng, final_deadline)
        if n2 > result[0] and lib.is_valid(n2, e2, d, D):
            result = (n2, e2)

    if not lib.is_valid(result[0], result[1], d, D):
        result = lib.haar_graph(d, range(d))
    return result
