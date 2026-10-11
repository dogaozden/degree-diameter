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
# Group tables. RT[s, g] = g * s (right multiplication), identity has index 0.
# Left multiplication is an automorphism of every lift built from these tables.
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
    """Z_m x|_r Z_k with (a1,b1)(a2,b2) = (a1 + r^{b1} a2, b1 + b2); element (a,b) coded a*k+b."""
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


def _inverses(RT):
    """inv[s] = s^{-1}; since g*s = e exactly when g = s^{-1}, read it off RT."""
    G = RT.shape[0]
    Z = np.argwhere(RT == 0)
    inv = np.empty(G, dtype=np.int64)
    inv[Z[:, 0]] = Z[:, 1]
    return inv


# ----------------------------------------------------------------------------
# NEW IDEA: multi-orbit bi-Cayley (voltage) lifts with b base vertices per side.
#
# Vertices: A_{i,g} (i < b, g in G) and B_{j,h}. Edge A_{i,g} -- B_{j, g*s} for
# each entry s of the set S_{ij}. The base matrix K[i][j] = |S_{ij}| has all row
# and column sums equal to d, so the lift is d-regular. Left multiplication by G
# is an automorphism, so the orbit representatives A_{i,e}, B_{j,e} (2b sources)
# suffice for the diameter check. This is richer than the single-orbit (b = 1)
# search: the order is 2*b*|G|, and the search space is larger at a fixed order.
# ----------------------------------------------------------------------------

def _random_K(b, d, rng):
    """Random nonnegative b x b integer matrix with all row and column sums d (sum of d permutations)."""
    K = np.zeros((b, b), dtype=np.int64)
    for _ in range(d):
        perm = list(range(b))
        rng.shuffle(perm)
        for i in range(b):
            K[i, perm[i]] += 1
    return K


def _init_state(b, d, G, K, rng):
    """J[i, t] = base label of slot t in row i (fixed); S[i, t] = group element (mutable)."""
    J = np.zeros((b, d), dtype=np.int64)
    S = np.zeros((b, d), dtype=np.int64)
    for i in range(b):
        labels = []
        for j in range(b):
            labels += [j] * int(K[i, j])
        rng.shuffle(labels)
        J[i] = labels
        for j in range(b):
            pos = [t for t in range(d) if labels[t] == j]
            vals = rng.sample(range(G), len(pos))
            for t, x in zip(pos, vals):
                S[i, t] = x
    return J, S


def _neighbors(b, G, RT, Ginv, J, S):
    """Neighbour table of shape (2bG, d). A ids: i*G + g. B ids: bG + j*G + h."""
    bG = b * G
    d = J.shape[1]
    NB = np.empty((2 * bG, d), dtype=np.int64)
    for i in range(b):
        cols = RT[S[i]]                                   # (d, G): g -> g*s
        Bids = bG + J[i][:, None] * G + cols
        NB[i * G:(i + 1) * G] = Bids.T
    for j in range(b):
        ii, tt = np.nonzero(J == j)                        # exactly d slots with label j
        rows = RT[Ginv[S[ii, tt]]]                         # (d, G): h -> h*s^{-1}
        Aids = ii[:, None] * G + rows
        NB[bG + j * G: bG + (j + 1) * G] = Aids.T
    return NB


def _cost(b, G, NB, D):
    """Number of (orbit representative, vertex) pairs at distance > D."""
    N = NB.shape[0]
    src = np.array([i * G for i in range(b)] + [b * G + j * G for j in range(b)],
                   dtype=np.int64)
    k = len(src)
    reach = np.zeros((k, N), dtype=bool)
    reach[np.arange(k), src] = True
    for _ in range(D):
        nxt = reach[:, NB].any(axis=2)
        nxt |= reach
        if np.array_equal(nxt, reach):
            break
        reach = nxt
    return k * N - int(reach.sum())


def _anneal(b, d, D, G, RT, Ginv, J, S, rng, deadline, iters):
    """Anneal entries of S (labels fixed) until cost 0. Returns True on success; S is modified in place."""
    cost = _cost(b, G, _neighbors(b, G, RT, Ginv, J, S), D)
    T0, T1 = 3.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        i = rng.randrange(b)
        t = rng.randrange(d)
        j = int(J[i, t])
        taken = set(int(x) for x in S[i][J[i] == j])
        x = rng.randrange(G)
        if x in taken:
            continue
        old = int(S[i, t])
        S[i, t] = x
        c2 = _cost(b, G, _neighbors(b, G, RT, Ginv, J, S), D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[i, t] = old
    return cost == 0


def _edges(b, G, NB):
    bG = b * G
    A = np.repeat(np.arange(bG, dtype=np.int64), NB.shape[1])
    Bv = NB[:bG].ravel()
    return list(zip(A.tolist(), Bv.tolist()))


def _search(d, D, best, deadline, rng):
    """Climb the order ladder separately for each base size b; keep only validated improvements."""
    lo = {b: max(d + 1, best[0] // (2 * b)) for b in (1, 2, 3)}
    delta = {1: 4, 2: 6, 3: 4}
    while time.monotonic() < deadline:
        b = rng.choices([1, 2, 3], weights=[1, 3, 2])[0]
        G = lo[b] + rng.randint(1, delta[b])
        G = max(G, best[0] // (2 * b) + 1, d + 1)
        if G > 900:
            break
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        Gg, RT = _table(opt)
        if Gg != G:
            continue
        Ginv = _inverses(RT)
        K = _random_K(b, d, rng)
        J, S = _init_state(b, d, G, K, rng)
        ok = _anneal(b, d, D, G, RT, Ginv, J, S, rng, deadline, 2500)
        if ok:
            n = 2 * b * G
            NB = _neighbors(b, G, RT, Ginv, J, S)
            if n > best[0]:
                e = _edges(b, G, NB)
                if lib.is_valid(n, e, d, D):
                    best = (n, e)
            lo[b] = max(lo[b], G)
            delta[b] = min(delta[b] + 1, 30)
        else:
            delta[b] = max(1, delta[b] - 1)
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

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])

    if D == 2 or best[0] >= lib._moore_bound(d, D):
        return best

    best = _search(d, D, best, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
