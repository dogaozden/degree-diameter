import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact families (kept from the parent as safe baselines).
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
# New family: greedy-built bi-Cayley lifts over Frobenius-type groups
# Z_m x| Z_k2 with m prime (k2 | m-1), plus cyclic groups.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s: A_{i,g} ~ B_{j,g*s}.
# Each layer is a permutation of blocks, so every vertex has degree d and
# edges stay distinct as long as the (j, s) pairs of each A-block are distinct.
#
# Search: layers are fixed at random, voltages are chosen greedily (the choice
# that minimises unreached (block, vertex) pairs among a random candidate
# pool), then a plateau local search refines them. This replaces the parent's
# annealing with a constructive start.
# ----------------------------------------------------------------------------

_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _is_prime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    f = 3
    while f * f <= n:
        if n % f == 0:
            return False
        f += 2
    return True


def _make_group(Gt, k2, rng):
    """Return (m, k2, r) with m * k2 >= Gt for Z_m x| Z_k2, or None."""
    if k2 == 1:
        return Gt, 1, 1
    m0 = -(-Gt // k2)
    for m in range(m0, m0 + 2000):
        if m > 2 and m % k2 == 1 % k2 and _is_prime(m):
            for _ in range(50):
                g = rng.randrange(2, m)
                r = pow(g, (m - 1) // k2, m)
                if r != 1:
                    return m, k2, r
            return None
    return None


def _semidirect_tables(m, k2, r):
    """Return (G, Ts, Invs) for Z_m x| Z_k2 (element a*k2+b, (a,b)(c,e) = (a+r^b c, b+e)).

    Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h.
    """
    G = m * k2
    x = np.arange(G, dtype=np.int64)
    a = x // k2
    b = x % k2
    powers = np.array([pow(r, t, m) for t in range(k2)], dtype=np.int64)
    M = ((a[:, None] + powers[b[:, None]] * a[None, :]) % m) * k2 + (b[:, None] + b[None, :]) % k2
    Ts = np.ascontiguousarray(M.T)  # Ts[s, g] = g*s
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return G, Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    """Write layer l's neighbours for A-block i and B-block j with voltage s."""
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bitmask per vertex: bit b set when representative block b is within distance D."""
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
    return reach


def _unreached(k, N, reach):
    """Number of unreached (representative, vertex) pairs."""
    return 2 * k * N - int(_POP[reach].sum())


def _trial(d, D, k, G, Ts, Invs, rng, deadline, cands, iters):
    """Greedy voltage assignment then plateau local search. Returns (n, edges) or None."""
    N = 2 * k * G
    layers = [rng.sample(range(k), k) for _ in range(d)]
    # Unset layers are identity (self-loops), which contribute nothing to reach.
    nbr = np.tile(np.arange(N, dtype=np.int64), (d, 1))
    S = [[0] * k for _ in range(d)]
    used = [set() for _ in range(k)]  # per A-block: set of (j, s) already used

    def cost():
        return _unreached(k, N, _reach(k, G, D, nbr, d))

    for l in range(d):
        for i in range(k):
            if time.monotonic() > deadline:
                return None
            j = layers[l][i]
            best_c, best_s = None, None
            pool = rng.sample(range(G), min(cands, G))
            for s in pool:
                if (j, s) in used[i]:
                    continue
                _set_dart(nbr, k, G, Ts, Invs, l, i, j, s)
                c = cost()
                if best_c is None or c < best_c or (c == best_c and rng.random() < 0.5):
                    best_c, best_s = c, s
            if best_s is None:
                return None
            S[l][i] = best_s
            used[i].add((j, best_s))
            _set_dart(nbr, k, G, Ts, Invs, l, i, j, best_s)

    cur = cost()
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        l = rng.randrange(d)
        i = rng.randrange(k)
        j = layers[l][i]
        new = rng.randrange(G)
        old = S[l][i]
        if new == old or (j, new) in used[i]:
            continue
        _set_dart(nbr, k, G, Ts, Invs, l, i, j, new)
        c = cost()
        if c <= cur:
            used[i].discard((j, old))
            used[i].add((j, new))
            S[l][i] = new
            cur = c
        else:
            _set_dart(nbr, k, G, Ts, Invs, l, i, j, old)

    if cur != 0:
        return None
    edges = set()
    for u in range(N):
        for l in range(d):
            v = int(nbr[l, u])
            if u != v:
                edges.add((min(u, v), max(u, v)))
    return N, sorted(edges)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    final_deadline = start + max(1.0, time_limit - 3.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return best

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

    # Main search: climb from the current best order.
    while time.monotonic() < deadline:
        k = rng.choice([1, 2, 2, 3, 4])
        k2 = rng.choice([1, 2, 3, 4, 6, 7])
        need = best_n + 2
        Gt = -(-need // (2 * k)) + rng.randrange(0, 3)
        grp = _make_group(Gt, k2, rng)
        if grp is None:
            continue
        m, k2, r = grp
        G, Ts, Invs = _semidirect_tables(m, k2, r)
        if 2 * k * G <= best_n:
            continue
        res = _trial(d, D, k, G, Ts, Invs, rng, deadline, cands=120, iters=1500)
        if res is not None:
            consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
