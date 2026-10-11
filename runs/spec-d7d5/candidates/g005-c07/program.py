import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Projective plane base (diameter 3).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (q kept small)."""
    for q in range(d - 1, 1, -1):
        if q > 40:
            continue
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Number-theory helpers for group construction.
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
# Group families. Each returns (G, RT) with RT[s, g] = g * s (right multiplication)
# and the identity at index 0. Left multiplication is an automorphism of the
# resulting bi-Cayley graph, so two BFS sources suffice for the diameter check.
# ----------------------------------------------------------------------------

def _affine_table(p, t):
    """Affine group {x -> a x + b over Z_p : a in H}, |H| = t, t | p-1. Order p*t.

    Element (a, b) is coded as pos(a) * p + b. Product: (a1,b1)(a2,b2) = (a1 a2, a1 b2 + b1).
    """
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
# Cayley-type search: connection set S of size d in G, edges A_g -- B_{g s}.
# Cost = number of (source, vertex) pairs unreached within D steps from A_e and B_e.
# ----------------------------------------------------------------------------

def _cost(Sa, RT, INV, G, D):
    RS = RT[Sa]
    IS = INV[Sa]
    total = 0
    for side0 in (0, 1):
        visA = np.zeros(G, dtype=bool)
        visB = np.zeros(G, dtype=bool)
        if side0 == 0:
            visA[0] = True
        else:
            visB[0] = True
        front = np.zeros(1, dtype=np.int64)
        side = side0
        for _ in range(D):
            mark = np.zeros(G, dtype=bool)
            if side == 0:
                mark[RS[:, front].ravel()] = True
                mark &= ~visB
                visB |= mark
            else:
                mark[IS[:, front].ravel()] = True
                mark &= ~visA
                visA |= mark
            front = np.flatnonzero(mark)
            side ^= 1
            if front.size == 0:
                break
        total += 2 * G - int(visA.sum()) - int(visB.sum())
    return total


def _anneal(d, D, G, RT, INV, rng, deadline, iters):
    """Anneal a connection set of size d; returns a zero-cost list S, or None."""
    if G < d + 1:
        return None
    S = rng.sample(range(G), d)
    cost = _cost(np.array(S, dtype=np.int64), RT, INV, G, D)
    T0, T1 = 2.0, 0.05
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        j = rng.randrange(d)
        x = rng.randrange(G)
        if x in S:
            continue
        old = S[j]
        S[j] = x
        c2 = _cost(np.array(S, dtype=np.int64), RT, INV, G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            cost = c2
        else:
            S[j] = old
    return list(S) if cost == 0 else None


def _cayley_phase(d, D, best, deadline, rng):
    """Climb the order ladder with affine/semidirect Cayley searches; return best validated (n, edges).

    Each round alternates between a ladder step (small order increase above the current
    best) and a stretch step that proposes a much larger group order, which is where
    the record-sized Cayley graphs live. Stretch steps get a larger annealing budget.
    """
    rnd = 0
    while time.monotonic() < deadline:
        rnd += 1
        lo = best[0] // 2 + 1
        if rnd % 3 == 0:
            # Stretch: propose orders well above the current best (up to ~1.15x),
            # with a bigger annealing budget.
            G = lo + 24 + rng.randrange(0, max(24, lo // 6))
            iters = 8000
        else:
            G = lo + rng.randrange(0, 24)
            iters = 3000
        if G > 1600:
            G = lo + rng.randrange(0, 24)
            if G > 1600:
                break
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        INV = np.argsort(RT, axis=1)
        S = _anneal(d, D, G2, RT, INV, rng, deadline, iters)
        if S is None:
            continue
        n = 2 * G2
        if n <= best[0]:
            continue
        e = []
        for s in S:
            row = RT[s].tolist()
            e.extend((g, G2 + row[g]) for g in range(G2))
        if lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
            best = (pg[0], pg[1])
        best = _cayley_phase(d, D, best, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
