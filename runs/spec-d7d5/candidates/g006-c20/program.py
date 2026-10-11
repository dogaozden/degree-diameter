import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Fallbacks and the diameter-3 projective plane.
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
# Number theory and finite groups given by right-multiplication tables.
# RT[s, g] = g * s, with the identity at index 0.
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
    RT = np.empty((G, G), dtype=np.int64)
    for s in range(G):
        a2 = H[s // p]
        b2 = s % p
        na = (A * a2) % p
        nb = (A * b2 + B) % p
        RT[s] = pos[na] * p + nb
    return G, RT


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k with (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2)."""
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
    """Candidate group descriptions of order exactly G."""
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
# Group-voltage lifts of small bipartite base multigraphs.
#
# Base graph: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, with d darts
# at every base vertex. Dart j = (U[j], V[j], Gv[j]) with U[j] in A, V[j] in B,
# and voltage g in G. The lift has vertices (A_u, x), (B_v, y) for x, y in G;
# edge (A_u, x) -- (B_v, x*g). Left multiplication by G is an automorphism, so
# it suffices to BFS from the 2k vertices (A_u, e) and (B_v, e).
# Cost = number of (source, vertex) pairs not reached within D steps, plus a
# penalty for duplicate darts.
# ----------------------------------------------------------------------------

def _lift_cost(U, V, Gv, k, d, G, RT, INV, D):
    kd = k * d
    n = 2 * k * G
    key = (U * k + V) * G + Gv
    dup = kd - int(np.unique(key).size)

    DA = np.arange(kd, dtype=np.int64).reshape(k, d)   # U is repeat(arange(k), d)
    DB = np.argsort(V, kind="stable").reshape(k, d)    # each V value appears d times

    # A-side neighbourhoods: (A_u, x) -> (B_v, x*g)
    MA = RT[Gv[DA]]                                    # (k, d, G)
    NA = (k * G + V[DA] * G)[:, :, None] + MA
    NA = NA.transpose(0, 2, 1).reshape(k * G, d)

    # B-side neighbourhoods: (B_v, y) -> (A_u, y*g^-1)
    MB = INV[Gv[DB]]                                   # (k, d, G)
    NB = (U[DB] * G)[:, :, None] + MB
    NB = NB.transpose(0, 2, 1).reshape(k * G, d)

    nbr = np.concatenate([NA, NB], axis=0)

    R = np.zeros((2 * k, n), dtype=bool)
    src = np.concatenate([np.arange(k) * G, k * G + np.arange(k) * G])
    R[np.arange(2 * k), src] = True
    for _ in range(D):
        R = R | R[:, nbr].any(axis=2)
    unreached = 2 * k * n - int(R.sum())
    return unreached + dup * n


def _anneal_lift(k, d, D, G, RT, INV, rng, deadline, iters):
    """Anneal voltages and B-endpoints; return (U, V, Gv) with zero cost, or None."""
    kd = k * d
    U = np.repeat(np.arange(k, dtype=np.int64), d)
    vl = list(U)
    rng.shuffle(vl)
    V = np.array(vl, dtype=np.int64)
    Gv = np.array([rng.randrange(G) for _ in range(kd)], dtype=np.int64)
    cost = _lift_cost(U, V, Gv, k, d, G, RT, INV, D)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if rng.random() < 0.5:
            j = rng.randrange(kd)
            old = int(Gv[j])
            Gv[j] = rng.randrange(G)
            c2 = _lift_cost(U, V, Gv, k, d, G, RT, INV, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                Gv[j] = old
        else:
            i = rng.randrange(kd)
            j = rng.randrange(kd)
            if V[i] == V[j]:
                continue
            V[i], V[j] = V[j], V[i]
            c2 = _lift_cost(U, V, Gv, k, d, G, RT, INV, D)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
                cost = c2
            else:
                V[i], V[j] = V[j], V[i]
    if cost == 0:
        return U, V, Gv
    return None


def _lift_edges(U, V, Gv, k, G, RT):
    off = k * G
    xs = np.arange(G, dtype=np.int64)
    edges = []
    for j in range(len(U)):
        u = int(U[j])
        v = int(V[j])
        g = int(Gv[j])
        a = (u * G + xs).tolist()
        b = (off + v * G + RT[g]).tolist()
        edges.extend(zip(a, b))
    return 2 * k * G, edges


def _lift_phase(d, D, best, deadline, rng):
    """Climb the order ladder with group-voltage lifts; return best validated (n, edges)."""
    rnd = 0
    while time.monotonic() < deadline:
        rnd += 1
        k = rng.choice((1, 2, 2, 3, 3, 4))
        lo = (best[0] + 2 * k) // (2 * k)      # smallest G with 2*k*G > best[0]
        span = 12 if rnd % 4 else max(12, lo // 10)   # occasional stretch jumps
        G = lo + rng.randrange(span)
        if G < 3 or G > 900:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        if G2 != G:
            continue
        INV = np.argsort(RT, axis=1)
        res = _anneal_lift(k, d, D, G2, RT, INV, rng, deadline, 2500)
        if res is None:
            continue
        U, V, Gv = res
        n, e = _lift_edges(U, V, Gv, k, G2, RT)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + max(0.0, min(0.75 * time_limit, time_limit - 5.0))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1:
        return 2, [(0, 1)]
    if D == 2:
        # K_{d,d}: diameter 2, order 2d, which is Moore-optimal for bipartite D = 2.
        return lib.haar_graph(d, range(d))

    # Safe fallback: K_{d,d}.
    best = lib.haar_graph(d, range(d))

    if D == 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])
        if lib.is_prime_power(d - 1):
            # Moore-optimal for D = 3 when d - 1 is a prime power.
            return best

    if D >= 3:
        best = _lift_phase(d, D, best, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
