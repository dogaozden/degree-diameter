import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Diameter-3 base: incidence graph of a projective plane.
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
    """Primitive root modulo an odd prime p."""
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
# Group multiplication tables. Every table T has T[x, y] = x * y, identity 0.
# ----------------------------------------------------------------------------

def _cyclic_table(G):
    X = np.arange(G, dtype=np.int64)
    return (X[:, None] + X[None, :]) % G


def _semidirect_table(m, k, r):
    """Z_m x|_r Z_k, element (a, b) coded a*k + b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2)."""
    G = m * k
    X = np.arange(G, dtype=np.int64)
    A = X // k
    B = X % k
    pw = np.array([pow(r, b, m) for b in range(k)], dtype=np.int64)
    A1, B1 = A[:, None], B[:, None]
    A2, B2 = A[None, :], B[None, :]
    return ((A1 + pw[B1] * A2) % m) * k + (B1 + B2) % k


def _affine_table(p, t):
    """{x -> a x + b : a in H}, |H| = t, t | p-1. Element (a, b) coded pos(a)*p + b."""
    g0 = _primitive_root(p)
    h = pow(g0, (p - 1) // t, p)
    H = np.array([pow(h, j, p) for j in range(t)], dtype=np.int64)
    pos = np.full(p, -1, dtype=np.int64)
    pos[H] = np.arange(t, dtype=np.int64)
    G = p * t
    X = np.arange(G, dtype=np.int64)
    A = H[X // p]
    B = X % p
    A1, B1 = A[:, None], B[:, None]
    A2, B2 = A[None, :], B[None, :]
    return pos[(A1 * A2) % p] * p + (A1 * B2 + B1) % p


def _group_tables(G, rng):
    """Shuffled list of multiplication tables of groups of order G (cyclic, affine, semidirect)."""
    tabs = [_cyclic_table(G)]
    for t in range(2, G + 1):
        if G % t:
            continue
        p = G // t
        if p >= 3 and _is_prime(p) and (p - 1) % t == 0:
            tabs.append(_affine_table(p, t))
    for k in range(2, min(G, 16) + 1):
        if G % k:
            continue
        m = G // k
        if m < 2:
            continue
        rs = [r for r in range(2, m)
              if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
        if rs:
            for r in rng.sample(rs, min(len(rs), 2)):
                tabs.append(_semidirect_table(m, k, r))
    rng.shuffle(tabs)
    return tabs


# ----------------------------------------------------------------------------
# Multi-base voltage lifts (new in this program).
#
# Base: k vertices A_0..A_{k-1} and k vertices B_0..B_{k-1}, joined by a
# d-regular bipartite multigraph given as d darts (i, j) per "round" (one random
# permutation per round). Each dart carries a voltage g in a group G of order G.
# Lift: A_{i,x} ~ B_{j, x*g} for all x in G. The lift is d-regular and bipartite
# with 2kG vertices, and left multiplication by G is an automorphism.
#
# Consequence used for the search: distance from any vertex is determined by
# distance from the 2k fibre representatives (x = identity). So the cost is the
# number of vertices unreached within D steps from those 2k sources only.
# ----------------------------------------------------------------------------

def _random_base(k, d, rng):
    pi, pj = [], []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        pi.extend(range(k))
        pj.extend(perm)
    return np.array(pi, dtype=np.int64), np.array(pj, dtype=np.int64)


def _initial_voltages(pi, pj, k, G, rng):
    """Random voltages, distinct within each base pair (so the lift stays simple)."""
    E = len(pi)
    pg = np.zeros(E, dtype=np.int64)
    groups = {}
    for e in range(E):
        groups.setdefault(int(pi[e]) * k + int(pj[e]), []).append(e)
    for mem in groups.values():
        if len(mem) > G:
            return None, None
        vals = rng.sample(range(G), len(mem))
        for e, v in zip(mem, vals):
            pg[e] = v
    return pg, groups


def _lift_nb(k, d, G, M, pi, pj, pg):
    """Neighbour array (n, d) of the lift. A-block indices 0..kG-1, B-block kG..2kG-1."""
    X = np.arange(G, dtype=np.int64)
    Ai = (pi[:, None] * G + X[None, :]).ravel()
    Bj = (k * G + pj[:, None] * G + M[X[None, :], pg[:, None]]).ravel()
    n = 2 * k * G
    verts = np.concatenate([Ai, Bj])
    tg = np.concatenate([Bj, Ai])
    order = np.argsort(verts, kind="stable")
    return tg[order].reshape(n, d)


def _unreached(nb, sources, D, n):
    """Total number of vertices not within distance D of the given sources."""
    total = 0
    for s in sources:
        seen = np.zeros(n, dtype=bool)
        seen[s] = True
        front = np.array([s], dtype=np.int64)
        for _ in range(D):
            cand = nb[front].ravel()
            cand = cand[~seen[cand]]
            if cand.size == 0:
                break
            front = np.unique(cand)
            seen[front] = True
        total += n - int(np.count_nonzero(seen))
    return total


def _anneal(k, d, G, M, pi, pj, pg, groups, keys, D, rng, deadline, iters):
    """Anneal voltages to zero unreached count. Returns True on success (pg modified)."""
    n = 2 * k * G
    E = len(keys)
    sources = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]

    def cost_now():
        return _unreached(_lift_nb(k, d, G, M, pi, pj, pg), sources, D, n)

    cost = cost_now()
    T0, T1 = 3.0, 0.05
    for it in range(iters):
        if cost == 0:
            break
        if it % 16 == 0 and time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        e = rng.randrange(E)
        used = {int(pg[f]) for f in groups[keys[e]] if f != e}
        cur = int(pg[e])
        avail = [g for g in range(G) if g not in used and g != cur]
        if not avail:
            continue
        pg[e] = rng.choice(avail)
        c2 = cost_now()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            pg[e] = cur
    return cost == 0


def _edges_from(k, G, M, pi, pj, pg):
    edges = []
    for e in range(len(pi)):
        i, j, g = int(pi[e]), int(pj[e]), int(pg[e])
        col = M[:, g].tolist()  # col[x] = x * g
        for x in range(G):
            edges.append((i * G + x, (k + j) * G + col[x]))
    return edges


def _try_lift(k, d, G, D, best_n, rng, deadline):
    """Try to find a k-base lift over a group of order G. Returns (n, edges) or None."""
    n = 2 * k * G
    tabs = _group_tables(G, rng)[:3]
    for M in tabs:
        for _ in range(2):
            if time.monotonic() >= deadline:
                return None
            pi, pj = _random_base(k, d, rng)
            pg, groups = _initial_voltages(pi, pj, k, G, rng)
            if pg is None:
                return None
            keys = [int(pi[e]) * k + int(pj[e]) for e in range(len(pi))]
            if _anneal(k, d, G, M, pi, pj, pg, groups, keys, D, rng, deadline, 2500):
                edges = _edges_from(k, G, M, pi, pj, pg)
                if n > best_n and lib.is_valid(n, edges, d, D):
                    return (n, edges)
    return None


def _lift_search(d, D, best, moore, deadline, rng):
    """Round-robin over base sizes k, climbing the group order for each k."""
    ks = [1, 3, 4, 2, 5, 6]
    nextG = {k: 0 for k in ks}
    while time.monotonic() < deadline:
        active = False
        for k in ks:
            if time.monotonic() >= deadline:
                break
            G = max(nextG[k], best[0] // (2 * k) + 1, 2)
            if 2 * k * G > moore:
                continue
            active = True
            nextG[k] = G
            attempt_deadline = min(deadline, time.monotonic() + 2.0)
            res = _try_lift(k, d, G, D, best[0], rng, attempt_deadline)
            if res is not None:
                best = res
                nextG[k] = G + 1
        if not active:
            break
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.75 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))

    if d == 2 and D >= 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return best

    if D >= 3 and d >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])

        moore = 2 * sum((d - 1) ** i for i in range(D))
        if best[0] < moore and time.monotonic() < deadline:
            best = _lift_search(d, D, best, moore, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
