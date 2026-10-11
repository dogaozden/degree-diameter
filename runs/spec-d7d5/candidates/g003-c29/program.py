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
# Group families. Each returns (G, RT) with RT[s, x] = x * s (right multiplication)
# and the identity at index 0.
# ----------------------------------------------------------------------------

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
# NEW: multi-orbit bi-Cayley (voltage lift over a group with k base vertices per side).
#
# Base graph: k "A" vertices and k "B" vertices, joined by d layers. Layer l is a
# permutation P[l] of range(k) plus voltages V[l][i] in G: A_i -- B_{P[l][i]} with
# voltage V[l][i]. Each base vertex has degree d. The lift has vertices (A_i, x),
# (B_j, y), x, y in G, with (A_i, x) ~ (B_j, x*s).
#
# Left multiplication is an automorphism, so every vertex is equivalent to a base
# vertex's identity. The diameter test therefore needs only 2k BFS sources.
# The cost counts ordered (source, vertex) pairs unreached within D steps.
# ----------------------------------------------------------------------------

def _darts(k, d, P, V, RT, INV):
    """Flatten the base graph into (i, j, RT[s], INV[s]) tuples."""
    out = []
    for l in range(d):
        for i in range(k):
            j = P[l][i]
            s = V[l][i]
            out.append((i, j, RT[s], INV[s]))
    return out


def _multi_cost(k, darts, G, D):
    """Number of ordered (source, vertex) pairs not reached within D steps."""
    total = 0
    for side0 in (0, 1):
        for idx0 in range(k):
            seen = [np.zeros((k, G), dtype=bool), np.zeros((k, G), dtype=bool)]
            cur = np.zeros((k, G), dtype=bool)
            cur[idx0, 0] = True
            seen[side0][idx0, 0] = True
            side = side0
            for _ in range(D):
                if not cur.any():
                    break
                nxt = np.zeros((k, G), dtype=bool)
                if side == 0:
                    # A_i -> B_j : (A_i, x) reaches (B_j, R[x]).
                    for i, j, R, _ in darts:
                        if cur[i].any():
                            row = nxt[j]
                            row[R] |= cur[i]
                else:
                    # B_j -> A_i : (B_j, y) reaches (A_i, Iv[y]).
                    for i, j, _, Iv in darts:
                        if cur[j].any():
                            row = nxt[i]
                            row[Iv] |= cur[j]
                other = 1 - side
                nxt &= ~seen[other]
                seen[other] |= nxt
                cur = nxt
                side = other
            total += 2 * k * G - int(seen[0].sum()) - int(seen[1].sum())
    return total


def _anneal_multi(k, d, D, G, RT, INV, rng, deadline, iters):
    """Anneal a k-orbit base graph over a group of order G; return (P, V) with zero cost, or None."""
    P = []
    for _ in range(d):
        perm = list(range(k))
        rng.shuffle(perm)
        P.append(perm)
    V = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    cost = _multi_cost(k, _darts(k, d, P, V, RT, INV), G, D)
    T0, T1 = 3.0, 0.1
    for it in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = T0 * (T1 / T0) ** (it / iters)
        l = rng.randrange(d)
        P2 = [p[:] for p in P]
        V2 = [v[:] for v in V]
        if k > 1 and rng.random() < 0.15:
            a, b = rng.sample(range(k), 2)
            P2[l][a], P2[l][b] = P2[l][b], P2[l][a]
        else:
            V2[l][rng.randrange(k)] = rng.randrange(G)
        c2 = _multi_cost(k, _darts(k, d, P2, V2, RT, INV), G, D)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / T):
            P, V, cost = P2, V2, c2
    return (P, V) if cost == 0 else None


def _lift_edges(k, G, RT, P, V):
    """Edge list of the lift: A_i,x -> i*G + x ; B_j,y -> k*G + j*G + y."""
    n = 2 * k * G
    edges = set()
    for l in range(len(P)):
        for i in range(k):
            j = P[l][i]
            R = RT[V[l][i]].tolist()
            for x in range(G):
                edges.add((i * G + x, k * G + j * G + R[x]))
    return n, sorted(edges)


def _multi_phase(d, D, best, deadline, rng):
    """Climb the order ladder with multi-orbit lifts; return best validated (n, edges)."""
    while time.monotonic() < deadline:
        k = rng.choice((1, 2, 2, 3))
        G = best[0] // (2 * k) + 1 + rng.randrange(0, 6)
        if G > 1200:
            continue
        opts = _group_options(G, rng)
        if not opts:
            continue
        opt = rng.choice(opts)
        G2, RT = _table(opt)
        INV = np.argsort(RT, axis=1)
        att_deadline = min(deadline, time.monotonic() + 6.0)
        res = _anneal_multi(k, d, D, G2, RT, INV, rng, att_deadline, 3000)
        if res is None:
            continue
        P, V = res
        n, e = _lift_edges(k, G2, RT, P, V)
        if n <= best[0]:
            continue
        if lib.is_valid(n, e, d, D):
            best = (n, e)
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
    if D == 2:
        return best

    pg = _best_pg(d)
    if pg is not None and pg[0] > best[0] and lib.is_valid(pg[0], pg[1], d, D):
        best = (pg[0], pg[1])

    # Incidence graph of PG(2, d-1) is Moore-optimal for D = 3: stop immediately.
    if D == 3 and d >= 3 and lib.is_prime_power(d - 1) and pg is not None:
        return best

    best = _multi_phase(d, D, best, deadline, rng)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
