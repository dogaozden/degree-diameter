import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Safe exact families (unchanged from the parent).
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
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _araujo_for(d):
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        try:
            return lib.araujo_lopez_graph(q)
        except Exception:
            return None
    return None


# ----------------------------------------------------------------------------
# New engine: bi-Cayley lifts over AGL(1, p) = Z_p x| Z_p^*, a non-abelian
# affine group (the parent used semidirect products Z_m x| Z_k).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h, G = p(p-1).
# Layer l joins A_i to B_{layers[l][i]} with voltage s: A_{i,g} ~ B_{p, g*s}.
# Each layer is a permutation of the base indices, so every vertex has degree d.
# Left multiplication is an automorphism, so distances from the k+k block
# representatives to all vertices decide the diameter.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP = np.array([bin(x).count("1") for x in range(1 << 16)], dtype=np.int64)


def _is_prime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True


def _moore(d, D):
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _affine_group(p):
    """Multiplication table of AGL(1,p). Element (a, b) with a in Z_p^*, b in Z_p, coded (a-1)*p + b.

    (a1, b1)(a2, b2) = (a1 a2, a1 b2 + b1). Identity is index 0.
    """
    G = p * (p - 1)
    idx = np.arange(G, dtype=np.int64)
    a = idx // p + 1
    b = idx % p
    A = (a[:, None] * a[None, :]) % p
    B = (a[:, None] * b[None, :] + b[:, None]) % p
    M = (A - 1) * p + B
    return G, M


def _tables(G, M):
    """Ts[s, g] = g*s and Invs[s, h] = the g with g*s = h."""
    x = np.arange(G, dtype=np.int64)
    Ts = np.ascontiguousarray(M.T)
    Invs = np.empty((G, G), dtype=np.int64)
    rows = np.arange(G)[:, None]
    Invs[rows, Ts] = np.broadcast_to(x[None, :], (G, G))
    return Ts, Invs


def _set_dart(nbr, k, G, Ts, Invs, l, i, j, s):
    nbr[l, i * G:(i + 1) * G] = (k + j) * G + Ts[s]
    nbr[l, (k + j) * G:(k + j + 1) * G] = i * G + Invs[s]


def _reach(k, G, D, nbr, d):
    """Bit b of reach[v] is set when representative of block b is within distance D of v."""
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


def _search(d, D, k, G, Ts, Invs, rng, deadline, iters, patience):
    """Simulated annealing over voltages and layer permutations. Returns (n, edges) or None."""
    N = 2 * k * G
    full = (1 << (2 * k)) - 1
    layers = [rng.sample(range(k), k) for _ in range(d)]
    S = [[rng.randrange(G) for _ in range(k)] for _ in range(d)]
    nbr = np.empty((d, N), dtype=np.int64)
    for l in range(d):
        for i in range(k):
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], S[l][i])

    def dupcount():
        keys = [(i, layers[l][i], S[l][i]) for l in range(d) for i in range(k)]
        return len(keys) - len(set(keys))

    def score(reach):
        return 2 * k * N - int(_POP[reach].sum()) + _PENALTY * dupcount()

    reach = _reach(k, G, D, nbr, d)
    cost = score(reach)
    c0 = float(max(cost, 1))
    best_cost = cost
    last = 0

    for t in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        if t - last > patience:
            break
        temp = max(0.3, 0.02 * c0 * (1.0 - t / iters))

        if k >= 2 and rng.random() < 0.2:
            l = rng.randrange(d)
            i1, i2 = rng.sample(range(k), 2)
            layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
            _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
            _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            r2 = _reach(k, G, D, nbr, d)
            c2 = score(r2)
            if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
                cost, reach = c2, r2
                if cost < best_cost:
                    best_cost, last = cost, t
            else:
                layers[l][i1], layers[l][i2] = layers[l][i2], layers[l][i1]
                _set_dart(nbr, k, G, Ts, Invs, l, i1, layers[l][i1], S[l][i1])
                _set_dart(nbr, k, G, Ts, Invs, l, i2, layers[l][i2], S[l][i2])
            continue

        bad = np.flatnonzero(reach != full) if rng.random() < 0.5 else None
        if bad is not None and bad.size:
            u = int(bad[rng.randrange(bad.size)])
            block = u // G
            l = rng.randrange(d)
            if block < k:
                i = block
            else:
                i = layers[l].index(block - k)
        else:
            l = rng.randrange(d)
            i = rng.randrange(k)

        old = S[l][i]
        new = rng.randrange(G)
        if new == old:
            continue
        S[l][i] = new
        _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], new)
        r2 = _reach(k, G, D, nbr, d)
        c2 = score(r2)
        if c2 <= cost or rng.random() < math.exp(-(c2 - cost) / temp):
            cost, reach = c2, r2
            if cost < best_cost:
                best_cost, last = cost, t
        else:
            S[l][i] = old
            _set_dart(nbr, k, G, Ts, Invs, l, i, layers[l][i], old)

    if cost != 0:
        return None
    edges = []
    for x in range(k * G):
        for l in range(d):
            edges.append((x, int(nbr[l, x])))
    return N, edges


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    try:
        if D >= 3:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
            if D == 3:
                ar = _araujo_for(d)
                if ar is not None:
                    consider(ar[0], ar[1])

        if D >= 4 and time.monotonic() < deadline:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
                if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                    return best

        # Candidate AGL(1,p) lifts, ascending by order.
        moore = _moore(d, D)
        cands = []
        for p in range(3, 46):
            if not _is_prime(p):
                continue
            G = p * (p - 1)
            for k in range(1, 9):
                n = 2 * k * G
                if n <= moore:
                    cands.append((n, k, p))
        cands.sort()

        while time.monotonic() < deadline - 0.5:
            live = [c for c in cands if c[0] > best_n]
            if not live:
                break
            for idx, (n, k, p) in enumerate(live):
                now = time.monotonic()
                if now >= deadline - 0.5:
                    break
                if n <= best_n:
                    continue
                remaining_c = len(live) - idx
                slice_end = min(deadline, now + max(1.0, (deadline - now) / remaining_c))
                G, M = _affine_group(p)
                Ts, Invs = _tables(G, M)
                while time.monotonic() < slice_end:
                    res = _search(d, D, k, G, Ts, Invs, rng, slice_end, 4000, 1000)
                    if res is not None:
                        consider(res[0], res[1])
                        break
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
