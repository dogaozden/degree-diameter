import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Basic helpers
# ----------------------------------------------------------------------------

def _moore(d, D):
    """Bipartite Moore bound for max degree d and diameter D."""
    if d <= 0 or D <= 0:
        return 1
    if d == 1:
        return 2
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _kdd(d):
    """K_{d,d}: diameter 2, valid whenever D >= 2."""
    return 2 * d, [(i, d + j) for i in range(d) for j in range(d)]


def _pg_base(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Group multiplication tables: MT[x, g] = x * g, identity code 0.
# ----------------------------------------------------------------------------

def _semi_table(m, k, r):
    """Z_m x|_r Z_k, (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2), element coded a*k+b."""
    G = m * k
    X = np.arange(G, dtype=np.int64)
    A = X // k
    B = X % k
    P = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    MT = ((A[:, None] + P[B][:, None] * A[None, :]) % m) * k + (B[:, None] + B[None, :]) % k
    return G, MT


def _ab_table(m1, m2):
    """Z_m1 x Z_m2."""
    G = m1 * m2
    X = np.arange(G, dtype=np.int64)
    A = X // m2
    B = X % m2
    MT = ((A[:, None] + A[None, :]) % m1) * m2 + (B[:, None] + B[None, :]) % m2
    return G, MT


def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = np.array([pow(h, j, p) for j in range(t)], dtype=np.int64)
    pos = np.full(p, -1, dtype=np.int64)
    pos[H] = np.arange(t, dtype=np.int64)
    G = p * t
    X = np.arange(G, dtype=np.int64)
    A = H[X // p]
    B = X % p
    newA = (A[:, None] * A[None, :]) % p
    newB = (A[:, None] * B[None, :] + B[:, None]) % p
    MT = pos[newA] * p + newB
    return G, MT


def _group_options(G, rng):
    opts = []
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
    for m1 in range(2, G):
        if m1 * m1 > G:
            break
        if G % m1 == 0 and G // m1 >= 2:
            opts.append(("ab", m1, G // m1))
    for t in range(1, G + 1):
        if G % t:
            continue
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            opts.append(("aff", p, t))
    return opts


def _table(opt):
    if opt[0] == "aff":
        return _affine_table(opt[1], opt[2])
    if opt[0] == "ab":
        return _ab_table(opt[1], opt[2])
    _, m, k, r = opt
    return _semi_table(m, k, r)


# ----------------------------------------------------------------------------
# Voltage lift of a bipartite base with k vertices per side, each of degree d.
# Base darts: slot j pairs A-vertex u with B-vertex sigs[j][u] via element gss[j][u].
# Lifted vertices: A (u,x) -> index u*G + x ; B (v,y) -> index k*G + v*G + y.
# Edge (u,x)-(v, x*g). Left multiplication is an automorphism, so BFS from the
# 2k base vertices (identity fibre) decides the diameter exactly.
# ----------------------------------------------------------------------------

def _make_nb(k, d, G, MT, INV, sigs, gss):
    n = 2 * k * G
    off = k * G
    NB = np.empty((n, d), dtype=np.int64)
    for j in range(d):
        sig = sigs[j]
        gl = gss[j]
        inv_sig = [0] * k
        for u in range(k):
            inv_sig[sig[u]] = u
        for u in range(k):
            v = sig[u]
            g = gl[u]
            NB[u * G:(u + 1) * G, j] = off + v * G + MT[:, g]
        for v in range(k):
            u = inv_sig[v]
            g = gl[u]
            NB[off + v * G: off + (v + 1) * G, j] = u * G + MT[:, INV[g]]
    return NB


def _cost(k, d, D, G, MT, INV, sigs, gss):
    keys = set()
    for j in range(d):
        for u in range(k):
            keys.add((u, sigs[j][u], gss[j][u]))
    dup = d * k - len(keys)
    if dup:
        return 10 ** 7 * dup
    NB = _make_nb(k, d, G, MT, INV, sigs, gss)
    n = 2 * k * G
    off = k * G
    srcs = [u * G for u in range(k)] + [off + v * G for v in range(k)]
    total = 0
    for s in srcs:
        vis = np.zeros(n, dtype=bool)
        vis[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            nb = NB[front].ravel()
            nb = nb[~vis[nb]]
            if nb.size == 0:
                break
            nb = np.unique(nb)
            vis[nb] = True
            front = nb
        total += n - int(vis.sum())
    return total


def _anneal(k, d, D, G, MT, INV, rng, t_end):
    sigs = []
    for _ in range(d):
        p = list(range(k))
        rng.shuffle(p)
        sigs.append(p)
    gss = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cur = _cost(k, d, D, G, MT, INV, sigs, gss)
    t0 = time.monotonic()
    span = max(t_end - t0, 1e-3)
    T0, T1 = 3.0, 0.05
    while cur > 0:
        now = time.monotonic()
        if now >= t_end:
            break
        T = T0 * (T1 / T0) ** min(1.0, (now - t0) / span)
        if k >= 2 and rng.random() < 0.25:
            j = rng.randrange(d)
            p, q = rng.sample(range(k), 2)
            sigs[j][p], sigs[j][q] = sigs[j][q], sigs[j][p]
            new = _cost(k, d, D, G, MT, INV, sigs, gss)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                sigs[j][p], sigs[j][q] = sigs[j][q], sigs[j][p]
        else:
            j = rng.randrange(d)
            u = rng.randrange(k)
            old = gss[j][u]
            gss[j][u] = rng.randrange(G)
            new = _cost(k, d, D, G, MT, INV, sigs, gss)
            if new <= cur or rng.random() < math.exp(-(new - cur) / T):
                cur = new
            else:
                gss[j][u] = old
    if cur == 0:
        return sigs, gss
    return None


def _edges_from_nb(k, d, G, NB):
    na = k * G
    A = np.repeat(np.arange(na, dtype=np.int64), d)
    Bv = NB[:na].ravel()
    return 2 * na, list(zip(A.tolist(), Bv.tolist()))


def _search(d, D, deadline, rng, box):
    """Anneal voltage lifts over varied groups and base sizes; improve box[0] in place."""
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = rng.choice((1, 1, 2, 2, 3))
        n_best = box[0][0]
        G = n_best // (2 * k) + 1 + rng.randrange(0, 6)
        if G < 2 or G > 1400:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        Gt, MT = _table(rng.choice(opts))
        if Gt != G:
            continue
        INV = np.argmax(MT == 0, axis=1)
        attempt_end = min(deadline, time.monotonic() + max(1.0, min(4.0, remaining / 3)))
        res = _anneal(k, d, D, G, MT, INV, rng, attempt_end)
        if res is None:
            continue
        sigs, gss = res
        NB = _make_nb(k, d, G, MT, INV, sigs, gss)
        n, edges = _edges_from_nb(k, d, G, NB)
        if n > box[0][0] and lib.is_valid(n, edges, d, D):
            box[0] = (n, edges)


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = min(0.8 * time_limit, time_limit - 5.0)
    deadline = start + max(0.0, budget)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    fallback = _kdd(d)
    if D == 2:
        return fallback

    box = [fallback]
    try:
        pg = _pg_base(d)
        if pg is not None and pg[0] > box[0][0] and lib.is_valid(pg[0], pg[1], d, D):
            box[0] = (pg[0], pg[1])
        if box[0][0] < _moore(d, D):
            _search(d, D, deadline, rng, box)
    except Exception:
        pass

    best = box[0]
    if lib.is_valid(best[0], best[1], d, D):
        return best
    return fallback
