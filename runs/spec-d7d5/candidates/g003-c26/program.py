import itertools
import math
import random
import time

import numpy as np

import lib

# Version notes:
# - Main search for D >= 3 is now a Haar-graph search over non-abelian groups
#   Z_m x| Z_k. A bipartite Haar graph H(G, S) has A_g ~ B_{g s} for s in S.
#   Left multiplication is an automorphism that is transitive on each side,
#   so the diameter equals the max eccentricity of A_e and B_e. Each candidate
#   costs two numpy BFS passes. Simulated annealing runs over the connection set S.
# - About a quarter of the iterations still run the parent's bi-Cayley search,
#   as a hedge against the new route stalling.
# - Exact constructions (PG(2,q), W(q)) and the K_{d,d} fallback are unchanged.

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


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
# Haar graphs over semidirect products Z_m x| Z_k (new main search).
# ----------------------------------------------------------------------------

def _group_tables(m, k, r):
    """Right-multiplication table R[s, g] = g*s and inverse array invs[s] = s^{-1}, element (a,b) coded a*k+b."""
    G = m * k
    codes = np.arange(G, dtype=np.int64)
    a = codes // k
    b = codes % k
    pw = np.array([pow(r, t, m) for t in range(k)], dtype=np.int64)
    c = codes // k
    dd = codes % k
    # g*s = (a_g + r^{b_g} c_s, b_g + d_s)
    R = ((a[None, :] + pw[b][None, :] * c[:, None]) % m) * k + (b[None, :] + dd[:, None]) % k
    # s^{-1} = (-r^{-d} c, -d)
    inv_a = (-pw[(-dd) % k] * c) % m
    inv_b = (-dd) % k
    invs = inv_a * k + inv_b
    return G, R.astype(np.int64), invs.astype(np.int64)


def _sample_semidirect(G, rng):
    """Random semidirect product Z_m x| Z_k of order G, preferring non-abelian ones. Returns (G, R, invs) or None."""
    ks = [k for k in range(1, 41) if G % k == 0 and G // k >= 2]
    if not ks:
        return None
    k = rng.choice(ks)
    m = G // k
    if k == 1:
        r = 1
    else:
        cands = [x for x in range(1, m) if math.gcd(x, m) == 1 and pow(x, k, m) == 1 % m]
        if not cands:
            return None
        nontriv = [x for x in cands if x != 1]
        if nontriv and rng.random() < 0.8:
            r = rng.choice(nontriv)
        else:
            r = rng.choice(cands)
    return _group_tables(m, k, r)


def _haar_cost(nbr, N, G, D):
    """Unreached vertices within distance D from A_e (index 0) and B_e (index G), summed."""
    total = 0
    for src in (0, G):
        seen = np.zeros(N, dtype=bool)
        seen[src] = True
        frontier = np.array([src], dtype=np.int64)
        for _ in range(D):
            nxt = nbr[:, frontier].ravel()
            nxt = nxt[~seen[nxt]]
            if nxt.size == 0:
                break
            frontier = np.unique(nxt)
            seen[frontier] = True
        total += N - int(seen.sum())
    return total


def _haar_search(d, D, G, R, invs, rng, deadline, iters):
    """Anneal a connection set S (|S| = d) so that H(G, S) has diameter <= D. Returns (n, edges) or None."""
    if G < d:
        return None
    N = 2 * G
    S = rng.sample(range(G), d)
    nbr = np.empty((d, N), dtype=np.int64)

    def write(l, s):
        nbr[l, :G] = G + R[s]
        nbr[l, G:] = R[invs[s]]

    for l, s in enumerate(S):
        write(l, s)
    inS = set(S)
    cost = _haar_cost(nbr, N, G, D)
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        new = rng.randrange(G)
        if new in inS:
            continue
        old = S[l]
        S[l] = new
        write(l, new)
        c2 = _haar_cost(nbr, N, G, D)
        temp = max(0.5, 0.05 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
            inS.discard(old)
            inS.add(new)
        else:
            S[l] = old
            write(l, old)

    if cost != 0:
        return None
    edges = []
    for l in range(d):
        for g in range(G):
            edges.append((g, int(nbr[l, g])))
    return N, edges


# ----------------------------------------------------------------------------
# Parent's bi-Cayley search (kept as a secondary route).
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order near target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        if k2 == 1:
            r = 1
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _tables(G, mul):
    """Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h, as contiguous int arrays."""
    Ts = np.array([[mul(g, s) for g in range(G)] for s in range(G)], dtype=np.int64)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(np.arange(G)[None, :], (G, G))
    return Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for base vertex i (A side) and base vertex j (B side) with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _cost(k, G, D, nbr):
    """Unreached (representative, vertex) pairs, computed for all representatives at once."""
    d, N = nbr.shape
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
    return 2 * k * N - int(_POP[reach].sum())


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side. Returns (n, edges) or None."""
    Ts, Invs = _tables(G, mul)
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    cost = _cost(k, G, D, nbr) + _PENALTY * dupcount()
    c0 = float(max(cost, 1))

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        c2 = _cost(k, G, D, nbr) + _PENALTY * dupcount()
        temp = max(0.5, 0.01 * c0 * (1.0 - t / iters))
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost = c2
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = set()
    for u in range(k * G):
        for v in nbr[:, u]:
            edges.add((u, int(v)))
    return N, sorted(edges)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search. Each round grows the target order just above the current best.
    while time.monotonic() < deadline:
        if rng.random() < 0.75:
            G = best_n // 2 + 1 + rng.randrange(0, 12)
            grp = _sample_semidirect(G, rng)
            if grp is None:
                continue
            G2, R, invs = grp
            res = _haar_search(d, D, G2, R, invs, rng, deadline, 2000)
            if res is not None:
                consider(res[0], res[1])
        else:
            k = rng.choice([1, 2, 2, 3, 4])
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            order, mul = g
            res = _search(d, D, k, order, mul, rng, deadline, 4000)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
