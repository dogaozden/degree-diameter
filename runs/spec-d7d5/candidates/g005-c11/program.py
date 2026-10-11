import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Number theory and finite group multiplication tables.
# Groups have order G <= ~800, stored as a full table M[x, y] = x*y with identity 0.
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


def _divisors(n):
    return [x for x in range(1, n + 1) if n % x == 0]


def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t, identity index 0."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = [pow(h, j, p) for j in range(t)]
    Hv = np.array(H, dtype=np.int64)
    pos = np.full(p, -1, dtype=np.int64)
    pos[Hv] = np.arange(t, dtype=np.int64)
    G = p * t
    X = np.arange(G, dtype=np.int64)[:, None]
    Y = np.arange(G, dtype=np.int64)[None, :]
    a1 = Hv[X // p]
    b1 = X % p
    a2 = Hv[Y // p]
    b2 = Y % p
    na = (a1 * a2) % p
    nb = (a1 * b2 + b1) % p
    M = pos[na] * p + nb
    return G, M


def _semi_table(m, k, r):
    """Z_m x|_r Z_k, element (a, b) coded a*k+b, identity 0."""
    G = m * k
    X = np.arange(G, dtype=np.int64)[:, None]
    Y = np.arange(G, dtype=np.int64)[None, :]
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    a1 = X // k
    b1 = X % k
    a2 = Y // k
    b2 = Y % k
    M = ((a1 + pw[b1] * a2) % m) * k + (b1 + b2) % k
    return G, M


def _group_options(G, rng):
    """Candidate group descriptions of order exactly G."""
    opts = []
    for t in _divisors(G):
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            opts.append(("aff", p, t))
    for k in _divisors(G):
        if k > 16:
            continue
        m = G // k
        if m < 2:
            continue
        opts.append(("semi", m, k, 1))
        if k > 1:
            rs = [r for r in range(2, m)
                  if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            if rs:
                for r in rng.sample(rs, min(3, len(rs))):
                    opts.append(("semi", m, k, r))
    return opts


def _make_group(opt):
    if opt[0] == "aff":
        G, M = _affine_table(opt[1], opt[2])
    else:
        _, m, k, r = opt
        G, M = _semi_table(m, k, r)
    inv = np.argmax(M == 0, axis=1).astype(np.int64)
    return G, M, inv


# ----------------------------------------------------------------------------
# Group voltage lifts of small bipartite base graphs.
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}.
# Darts: for each perm sigma_t (t < d) and each i, dart (A_i -> B_{sigma_t(i)}, voltage g).
# Lift: A_i x  --  B_j (x*g) for every dart. Every vertex has degree d.
# Vertex index: A_i element x -> i*G + x ; B_j element y -> (k+j)*G + y.
# Left multiplication is an automorphism, so BFS from (u, e) for each base vertex u
# checks the diameter completely.
# ----------------------------------------------------------------------------

def _build_nb(V, k, d, G, M, inv, Jt, INt):
    N = 2 * k * G
    NB = np.empty((N, d), dtype=np.int64)
    for i in range(k):
        Gt = V[i * d:(i + 1) * d]
        tgt = Jt[i * d:(i + 1) * d] + k
        NB[i * G:(i + 1) * G] = tgt[None, :] * G + M[:, Gt]
    for j in range(k):
        idx = INt[j]
        src = idx // d
        Vin = inv[V[idx]]
        NB[(k + j) * G:(k + j + 1) * G] = src[None, :] * G + M[:, Vin]
    return NB


def _cost(NB, k, G, D):
    """Total number of (base source, vertex) pairs unreached within D steps."""
    N = NB.shape[0]
    total = 0
    for u in range(2 * k):
        s = u * G
        vis = np.zeros(N, dtype=bool)
        vis[s] = True
        fr = np.array([s], dtype=np.int64)
        for _ in range(D):
            mk = np.zeros(N, dtype=bool)
            mk[NB[fr].ravel()] = True
            mk &= ~vis
            if not mk.any():
                break
            vis |= mk
            fr = np.flatnonzero(mk)
        total += N - int(vis.sum())
    return total


def _lift_search(k, d, D, G, M, inv, rng, attempt_end, deadline):
    """Anneal dart voltages; return (V, Jt) with zero cost, or None."""
    end_time = min(attempt_end, deadline)
    perms = [rng.sample(range(k), k) for _ in range(d)]
    Jt = np.array([perms[tt][i] for i in range(k) for tt in range(d)], dtype=np.int64)
    INt = [np.flatnonzero(Jt == j) for j in range(k)]
    L = k * d
    V = np.array([rng.randrange(G) for _ in range(L)], dtype=np.int64)
    NB = _build_nb(V, k, d, G, M, inv, Jt, INt)
    cost = _cost(NB, k, G, D)
    T0, T1 = 3.0, 0.2
    t0 = time.monotonic()
    span = max(1e-3, end_time - t0)
    while cost > 0:
        now = time.monotonic()
        if now >= end_time:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        t = rng.randrange(L)
        old = int(V[t])
        V[t] = rng.randrange(G)
        NB2 = _build_nb(V, k, d, G, M, inv, Jt, INt)
        c2 = _cost(NB2, k, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            NB = NB2
        else:
            V[t] = old
    if cost == 0:
        return V.copy(), Jt
    return None


def _lift_edges(V, Jt, k, d, G, M):
    e = set()
    for t in range(k * d):
        i = t // d
        j = int(Jt[t])
        g = int(V[t])
        ys = M[:, g]
        for x in range(G):
            e.add((i * G + x, (k + j) * G + int(ys[x])))
    return list(e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.5, min(0.8 * time_limit, time_limit - 4.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        return best

    moore = lib._moore_bound(d, D)
    if best[0] >= moore:
        return best

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])

        while time.monotonic() < deadline and best[0] < moore:
            k = rng.choice([1, 2, 2, 3, 3, 4])
            nmin = best[0] // (2 * k) + 1
            G = nmin + rng.randrange(0, 6)
            if G < 2 or G > 800:
                continue
            opts = _group_options(G, rng)
            if not opts:
                continue
            G, M, inv = _make_group(rng.choice(opts))
            now = time.monotonic()
            remaining = deadline - now
            if remaining <= 0.2:
                break
            attempt_end = now + min(remaining, 4.0 + 6.0 * rng.random())
            res = _lift_search(k, d, D, G, M, inv, rng, attempt_end, deadline)
            if res is None:
                continue
            V, Jt = res
            n = 2 * k * G
            if n <= best[0]:
                continue
            e = _lift_edges(V, Jt, k, d, G, M)
            if lib.is_valid(n, e, d, D):
                best = (n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
