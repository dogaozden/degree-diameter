import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1 (q kept small)."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Number-theory helpers and group families.
# Each table has RT[s, g] = g * s (right multiplication) with identity at index 0.
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
# Multi-orbit voltage lifts.
# Base: k A-vertices and k B-vertices, every vertex of degree d.
# Slot s (0..d-1) joins A_i to B_{perm_s(i)} with voltage volt[i, s] in G:
#   A_{i,x} -- B_{perm_s(i), x * volt[i,s]}.
# Since each perm_s is a bijection, every B-vertex also has degree d.
# Left multiplication is an automorphism, so BFS from A_{i,e} and B_{j,e}
# (2k sources) certifies the diameter.
# ----------------------------------------------------------------------------

def _neighbors(k, G, d, RT, INV, perms, volt):
    """Neighbour array of shape (2kG, d). A-vertex i*G+x; B-vertex kG + j*G + y."""
    n = 2 * k * G
    Nbr = np.empty((n, d), dtype=np.int64)
    pinv = np.empty_like(perms)
    for s in range(d):
        pinv[s, perms[s]] = np.arange(k)
    for i in range(k):
        for s in range(d):
            j = int(perms[s, i])
            v = int(volt[i, s])
            Nbr[i * G:(i + 1) * G, s] = k * G + j * G + RT[v]
    for j in range(k):
        for s in range(d):
            i = int(pinv[s, j])
            v = int(volt[i, s])
            Nbr[k * G + j * G:k * G + (j + 1) * G, s] = i * G + INV[v]
    return Nbr


def _cost(Nbr, srcs, D, n):
    """Total number of (source, vertex) pairs not reached within D steps."""
    S = srcs.shape[0]
    deg = Nbr.shape[1]
    reach = np.zeros((S, n), dtype=bool)
    reach[np.arange(S), srcs] = True
    frontier = reach.copy()
    for _ in range(D):
        rows, cols = np.nonzero(frontier)
        if rows.size == 0:
            break
        tg = Nbr[cols].ravel()
        rr = np.repeat(rows, deg)
        new = np.zeros((S, n), dtype=bool)
        new[rr, tg] = True
        new &= ~reach
        if not new.any():
            break
        reach |= new
        frontier = new
    return S * n - int(reach.sum())


def _anneal_multi(d, D, k, G, RT, INV, rng, deadline, iters):
    """Anneal permutations and voltages; return (perms, volt) with zero cost, or None."""
    n = 2 * k * G
    srcs = np.array([i * G for i in range(k)] + [k * G + j * G for j in range(k)],
                    dtype=np.int64)
    perms = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    volt = np.array([[rng.randrange(G) for _ in range(d)] for _ in range(k)],
                    dtype=np.int64)
    Nbr = _neighbors(k, G, d, RT, INV, perms, volt)
    cost = _cost(Nbr, srcs, D, n)
    cost0 = max(cost, 1)
    T0 = max(1.0, 0.05 * cost0)
    T1 = 0.5
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        if k > 1 and rng.random() < 0.15:
            s = rng.randrange(d)
            old_p = perms[s].copy()
            perms[s] = np.array(rng.sample(range(k), k), dtype=np.int64)
            undo = ("p", s, old_p)
        else:
            i = rng.randrange(k)
            s = rng.randrange(d)
            old_v = int(volt[i, s])
            volt[i, s] = rng.randrange(G)
            undo = ("v", i, s, old_v)
        Nbr2 = _neighbors(k, G, d, RT, INV, perms, volt)
        c2 = _cost(Nbr2, srcs, D, n)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
            Nbr = Nbr2
        else:
            if undo[0] == "p":
                perms[undo[1]] = undo[2]
            else:
                volt[undo[1], undo[2]] = undo[3]
    if cost == 0:
        return perms, volt
    return None


def _edges_from(k, G, d, RT, INV, perms, volt):
    """Build (n, sorted edge list) from a successful parameter set."""
    Nbr = _neighbors(k, G, d, RT, INV, perms, volt)
    n = 2 * k * G
    edges = set()
    for a in range(k * G):
        for s in range(d):
            edges.add((a, int(Nbr[a, s])))
    return n, sorted(edges)


def _search(d, D, best, deadline, rng, ks, iters):
    """Ladder search over group orders; keeps the largest validated graph found."""
    while time.monotonic() < deadline:
        if best[0] >= 2400:
            break
        k = rng.choice(ks)
        lo = best[0] // (2 * k) + 1
        G = lo + rng.randrange(0, 12)
        if 2 * k * G > 2400:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        if G2 != G:
            continue
        INV = np.argsort(RT, axis=1)
        res = _anneal_multi(d, D, k, G, RT, INV, rng, deadline, iters)
        if res is None:
            continue
        perms, volt = res
        n, edges = _edges_from(k, G, d, RT, INV, perms, volt)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    pg = _best_pg(d) if D >= 3 else None
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = (pg[0], pg[1])
        # Projective plane with q = d-1 is Moore-optimal for D = 3; return at once.
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1) and d - 1 <= 40:
            return best

    if D >= 3 and budget > 0:
        # Phase 1: cyclic-style bi-Cayley search (safe baseline, about 30% of budget).
        phase1_end = start + 0.3 * budget
        best = _search(d, D, best, min(phase1_end, deadline), rng, [1], 6000)
        # Phase 2: bold multi-orbit voltage lifts over non-cyclic groups.
        best = _search(d, D, best, deadline, rng, [2, 2, 3, 3, 4, 4, 5, 6], 8000)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
