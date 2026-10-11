import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# New construction: non-regular-looking voltage lifts with many base vertices
# (k up to 12 per side) over small groups, found by annealing the voltages
# directly on the lifted graph. Groups are cyclic Z_m or semidirect
# Z_m x| Z_k2 given by explicit multiplication tables.
#
# Vertices: A-block i (0..k-1) -> indices i*G + x; B-block j -> (k+j)*G + y.
# Layer l joins A(i, x) to B(P[l,i], x * S[l,i]) (right multiplication).
# The group acts by left multiplication as automorphisms, so distances from
# all vertices to one representative per block determine the diameter.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)
_PEN = 200


def _cyclic_table(m):
    a = np.arange(m, dtype=np.int64)
    M = (a[:, None] + a[None, :]) % m
    Inv = (-a) % m
    return M, Inv


def _semidirect_table(m, k2, r):
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    pw = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + pw[b][:, None] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    rr, cc = np.nonzero(M == 0)
    Inv = np.empty(G, dtype=np.int64)
    Inv[rr] = cc
    return M, Inv


def _sample_group(Gt, rng):
    """Return (M, Inv) for a group of order >= Gt (cyclic or semidirect)."""
    if rng.random() < 0.5:
        return _cyclic_table(max(2, Gt))
    k2 = rng.choice([2, 3, 4, 6])
    m = max(2, -(-Gt // k2))
    cands = [m - 1] if m > 2 else []
    for _ in range(30):
        cands.append(rng.randrange(2, m) if m > 2 else 1)
    for r in cands:
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return _semidirect_table(m, k2, r)
    return _cyclic_table(max(2, Gt))


def _layer_rows(k, G, M, Inv, p, s, nbr, l):
    """Write layer l's neighbours for all vertices from permutation p and voltages s."""
    ar = np.arange(G, dtype=np.int64)
    A = (k + p)[:, None] * G + M[ar[None, :], s[:, None]]
    nbr[l, :k * G] = A.reshape(-1)
    inv = np.empty(k, dtype=np.int64)
    inv[p] = np.arange(k, dtype=np.int64)
    sinv = Inv[s[inv]]
    B = inv[:, None] * G + M[ar[None, :], sinv[:, None]]
    nbr[l, k * G:] = B.reshape(-1)


def _cost(k, G, nbr, D, d):
    """Number of unreached (vertex, block representative) pairs at distance > D."""
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
    pop = int(_POP[reach & 0xFFFF].sum() + _POP[(reach >> 16) & 0xFFFF].sum())
    return 2 * k * N - pop


def _dups(P, S, G):
    """Number of repeated (base B-vertex, voltage) pairs per base A-vertex (each is a multi-edge)."""
    keys = P * G + S
    dup = 0
    for i in range(keys.shape[1]):
        dup += keys.shape[0] - len(set(keys[:, i].tolist()))
    return dup


def _search(d, D, k, M, Inv, rng, deadline, iters, patience):
    """Anneal permutations and voltages. Returns (n, edges) if diameter <= D is reached, else None."""
    G = M.shape[0]
    N = 2 * k * G
    P = np.array([rng.sample(range(k), k) for _ in range(d)], dtype=np.int64)
    S = np.array([[rng.randrange(G) for _ in range(k)] for _ in range(d)], dtype=np.int64)
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        _layer_rows(k, G, M, Inv, P[l], S[l], nbr, l)

    def total():
        return _cost(k, G, nbr, D, d) + _PEN * _dups(P, S, G)

    cost = total()
    T0 = max(1.0, 0.02 * cost)
    best_cost, last = cost, 0
    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline or t - last > patience:
            break
        temp = max(0.3, T0 * (1.0 - t / iters))
        l = rng.randrange(d)
        swap = k >= 2 and rng.random() < 0.3
        if swap:
            i1, i2 = rng.sample(range(k), 2)
            P[l, i1], P[l, i2] = P[l, i2], P[l, i1]
        else:
            i = rng.randrange(k)
            old = int(S[l, i])
            new = rng.randrange(G)
            if new == old:
                continue
            S[l, i] = new
        _layer_rows(k, G, M, Inv, P[l], S[l], nbr, l)
        c2 = total()
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            if swap:
                P[l, i1], P[l, i2] = P[l, i2], P[l, i1]
            else:
                S[l, i] = old
            _layer_rows(k, G, M, Inv, P[l], S[l], nbr, l)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for l in range(d):
            edges.add((u, int(nbr[l, u])))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    final = start + max(1.0, min(time_limit - 6.0, 0.9 * time_limit))
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() < final:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 2 and D >= 2:
        KS = (3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
        while True:
            now = time.monotonic()
            if now > final - 1.0:
                break
            k = rng.choice(KS)
            Gt = max(2, best_n // (2 * k) + 1 + rng.randrange(0, 1 + best_n // (2 * k * 8)))
            M, Inv = _sample_group(Gt, rng)
            G = M.shape[0]
            if 2 * k * G <= best_n:
                continue
            att = min(final, now + max(2.0, (final - now) / 3.0))
            try:
                res = _search(d, D, k, M, Inv, rng, att, 80000, 2500)
            except Exception:
                res = None
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
