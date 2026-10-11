import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Bounds and simple candidates.
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Moore bound for bipartite graphs with max degree d and diameter D."""
    if D <= 0 or d <= 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q <= 40)."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo & Lopez graph for d = q + 2 with q a prime power >= 3, else None."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# Group tables. RT[s, g] = g * s, identity at index 0.
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


def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t. Element (a, b) coded pos(a)*p + b."""
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
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        RT[s] = pos[na] * p + nb
    return G, RT


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k, element (a, b) coded a*k + b, product (a1 + r^{b1} a2, b1 + b2)."""
    G = m * k
    idx = np.arange(G, dtype=np.int64)
    A = idx // k
    B = idx % k
    powr = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    PB = powr[B]
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        c, dd = divmod(s, k)
        RT[s] = ((A + PB * c) % m) * k + (B + dd) % k
    return G, RT


def _group_options(G, rng):
    opts = []
    for t in range(1, G + 1):
        if G % t:
            continue
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            opts.append(("aff", p, t))
    for k in range(1, min(G, 16) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        opts.append(("semi", m, k, 1))
        if k > 1:
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                for r in rng.sample(rs, min(len(rs), 3)):
                    opts.append(("semi", m, k, r))
    return opts


def _table(opt):
    if opt[0] == "aff":
        return _affine_table(opt[1], opt[2])
    _, m, k, r = opt
    return _semidirect_table(m, k, r)


# ----------------------------------------------------------------------------
# Multi-orbit voltage lift.
# Base: a vertices on side A, a on side B. Darts (u, v, s) join (u, x) to (v, x*s).
# The lift has 2a*m vertices and is regular of degree d when every base vertex
# has exactly d darts. Left multiplication is an automorphism, so BFS from
# (w, e) for each base vertex w checks the diameter.
# ----------------------------------------------------------------------------

def _pattern(a, d, rng):
    """Regular a x a dart pattern: sum of d random permutation matrices (row and column sums d)."""
    M = [[0] * a for _ in range(a)]
    for _ in range(d):
        p = list(range(a))
        rng.shuffle(p)
        for i in range(a):
            M[i][p[i]] += 1
    U, V = [], []
    for i in range(a):
        for j in range(a):
            for _ in range(M[i][j]):
                U.append(i)
                V.append(j)
    return U, V


def _edges_arr(Ua, Va, Sarr, RT, X, m):
    """Directed edge arrays (src, dst) of the lift, both directions included."""
    srcf = (Ua[:, None] * m + X[None, :]).ravel()
    dstf = (Va[:, None] * m + RT[Sarr]).ravel()
    return np.concatenate((srcf, dstf)), np.concatenate((dstf, srcf))


def _cost(src, dst, n, nb, m, D):
    """Total number of (source, vertex) pairs unreached within D steps, over all base sources."""
    total = 0
    for w in range(nb):
        vis = np.zeros(n, dtype=bool)
        fr = np.zeros(n, dtype=bool)
        s0 = w * m
        vis[s0] = True
        fr[s0] = True
        for _ in range(D):
            cand = dst[fr[src]]
            new = cand[~vis[cand]]
            if new.size == 0:
                break
            vis[new] = True
            fr = np.zeros(n, dtype=bool)
            fr[new] = True
        total += n - int(np.count_nonzero(vis))
    return total


def _anneal(a, m, RT, U, V, S, rng, deadline, iters, D):
    """Anneal group labels of darts so that each pair's labels stay distinct. Returns S or None."""
    nb = 2 * a
    n = nb * m
    N = len(U)
    X = np.arange(m, dtype=np.int64)
    Ua = np.asarray(U, dtype=np.int64)
    Va = np.asarray(V, dtype=np.int64) + a
    used = {}
    for i in range(N):
        used.setdefault((U[i], V[i]), set()).add(S[i])
    Sarr = np.asarray(S, dtype=np.int64)
    src, dst = _edges_arr(Ua, Va, Sarr, RT, X, m)
    cost = _cost(src, dst, n, nb, m, D)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(N)
        key = (U[i], V[i])
        s_new = rng.randrange(m)
        if s_new in used[key]:
            continue
        old = S[i]
        Sarr[i] = s_new
        src2, dst2 = _edges_arr(Ua, Va, Sarr, RT, X, m)
        c2 = _cost(src2, dst2, n, nb, m, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            src, dst = src2, dst2
            used[key].discard(old)
            used[key].add(s_new)
            S[i] = s_new
        else:
            Sarr[i] = old
    return S if cost == 0 else None


def _try_lift(d, D, a, m, rng, deadline, iters):
    """One randomized attempt at a 2a*m-vertex lift of degree d. Returns (n, edges) or None."""
    opts = _group_options(m, rng)
    if not opts:
        return None
    opt = rng.choice(opts)
    G, RT = _table(opt)
    if G != m:
        return None
    U, V = _pattern(a, d, rng)
    used = {}
    S = []
    for i in range(len(U)):
        key = (U[i], V[i])
        bag = used.setdefault(key, set())
        s = rng.randrange(m)
        while s in bag:
            s = rng.randrange(m)
        bag.add(s)
        S.append(s)
    S = _anneal(a, m, RT, U, V, S, rng, deadline, iters, D)
    if S is None:
        return None
    n = 2 * a * m
    edges = []
    for i in range(len(U)):
        u = U[i] * m
        v = (a + V[i]) * m
        row = RT[S[i]].tolist()
        edges.extend((u + x, v + row[x]) for x in range(m))
    return n, edges


def _lift_phase(d, D, best, moore, deadline, rng):
    """Climb the order ladder with multi-orbit lifts; return the best validated (n, edges)."""
    while time.monotonic() < deadline:
        if best[0] >= moore:
            break
        a = rng.choice((1, 2, 2, 3, 3, 4, 5))
        nb = 2 * a
        m_min = max(best[0] // nb + 1, d + 1)
        if nb * m_min > moore:
            continue
        m = m_min + rng.randrange(0, max(3, m_min // 12))
        m = min(m, moore // nb, 1000)
        if m < m_min:
            continue
        res = _try_lift(d, D, a, m, rng, deadline, 6000)
        if res is not None and res[0] > best[0] and lib.is_valid(res[0], res[1], d, D):
            best = res
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        moore = _moore(d, D)
        if best[0] < moore:
            for cand in (_best_pg(d), _araujo(d)):
                if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                    best = (cand[0], cand[1])
        if d >= 2 and best[0] < moore:
            best = _lift_phase(d, D, best, moore, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], best[1]
