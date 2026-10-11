import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# Exact algebraic families.
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
# Random d-regular bipartite graphs repaired by edge-switch annealing.
# Left vertices 0..n-1, right vertices n..2n-1.
# ----------------------------------------------------------------------------

_PENALTY = 1000
_POP8 = np.array([bin(i).count("1") for i in range(256)], dtype=np.int64)
_POP16 = np.array([bin(i).count("1") for i in range(1 << 16)], dtype=np.int64)


def _rr_base(N, W):
    base = np.zeros((N, W), dtype=np.uint64)
    v = np.arange(N, dtype=np.int64)
    base[v, v // 64] = np.uint64(1) << (v % 64).astype(np.uint64)
    return base


def _rr_cost(n, d, EB, D, N, base):
    E2 = EB.reshape(n, d)
    order = np.argsort(EB, kind="stable")
    nb = np.empty((N, d), dtype=np.int64)
    nb[:n] = n + E2
    nb[n:] = (order // d).reshape(n, d)
    R = base
    for _ in range(D):
        R = R | np.bitwise_or.reduce(R[nb], axis=1)
    reached = int(_POP8[R.view(np.uint8)].sum())
    srt = np.sort(E2, axis=1)
    dup = int(np.count_nonzero(srt[:, 1:] == srt[:, :-1]))
    return N * N - reached + _PENALTY * dup


def _rr_search(n, d, D, rng, deadline):
    N = 2 * n
    W = (N + 63) // 64
    base = _rr_base(N, W)
    perms = [rng.sample(range(n), n) for _ in range(d)]
    EB = np.array(perms, dtype=np.int64).T.copy().ravel()
    M = n * d
    cur = _rr_cost(n, d, EB, D, N, base)
    t0 = time.monotonic()
    span = max(1e-3, deadline - t0)
    while cur != 0:
        now = time.monotonic()
        if now > deadline:
            break
        frac = (now - t0) / span
        temp = 8.0 * (0.03 ** frac) + 0.05
        e1 = rng.randrange(M)
        e2 = rng.randrange(M)
        if EB[e1] == EB[e2]:
            continue
        EB[e1], EB[e2] = EB[e2], EB[e1]
        c2 = _rr_cost(n, d, EB, D, N, base)
        if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / temp):
            cur = c2
        else:
            EB[e1], EB[e2] = EB[e2], EB[e1]
    if cur != 0:
        return None
    E2 = EB.reshape(n, d).tolist()
    edges = set()
    for i in range(n):
        for j in E2[i]:
            edges.add((i, n + j))
    return N, sorted(edges)


def _rr_arm(d, D, rng, deadline):
    moore = 2 * sum((d - 1) ** i for i in range(D))
    cap = 1500
    side = max(d + 1, min(cap, int(0.3 * moore / 2)))
    lo = None
    hi = None
    best = None
    while time.monotonic() < deadline - 0.5:
        now = time.monotonic()
        remaining = deadline - now
        slice_end = min(deadline, now + max(3.0, 0.3 * remaining))
        res = _rr_search(side, d, D, rng, slice_end)
        if res is not None:
            if best is None or res[0] > best[0]:
                best = res
            lo = side
            if side >= cap:
                break
            if hi is None:
                side = int(side * 1.06) + 1
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        else:
            hi = side
            if lo is None:
                side = int(side * 0.94)
            else:
                if hi - lo <= 1:
                    break
                side = (lo + hi) // 2
        side = min(max(side, d + 1), cap)
    return best


# ----------------------------------------------------------------------------
# Bi-Cayley lifts over semidirect products Z_m x| Z_k2 (bit-parallel cost).
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{j,h} = (k+j)*G + h.
# Each of the d layers is a permutation p of range(k) with a voltage s per
# base vertex: A_{i,g} ~ B_{p[i], g*s}. Every vertex then has degree d.
# Left multiplication is an automorphism, so the 2k block starts represent
# all vertex orbits; the diameter check only needs those 2k sources.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (order, mul) for a semidirect product Z_m x| Z_k2 of order near target, or None.

    r = 1 (a direct product) is always a valid fallback, so groups whose
    orders have no nontrivial automorphism of the required kind still appear.
    """
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, target // k2)
        r = 1
        if k2 > 1:
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
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
    """Unreached (representative, vertex) pairs over the 2k orbit representatives."""
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
    return 2 * k * N - int(_POP16[reach].sum())


def _search(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over the voltages of a base with k vertices per side.

    Returns (n, edges) with diameter <= D, or None.
    """
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


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.8 * time_limit, time_limit - 8.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1 or d == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions (calibration-style cases return immediately).
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

    # Arm 1: random regular bipartite graphs repaired by edge-switch annealing.
    if D >= 3 and d >= 3 and time.monotonic() < deadline:
        rr_deadline = start + 0.15 * budget
        try:
            res = _rr_arm(d, D, rng, rr_deadline)
            if res is not None:
                consider(res[0], res[1])
        except Exception:
            pass

    # Arm 2: bi-Cayley lifts over semidirect products, sweeping group orders
    # just above the current best (per side: best_n / (2k)).
    try:
        while time.monotonic() < deadline - 0.5:
            now = time.monotonic()
            remaining = deadline - now
            k = rng.choice([1, 1, 2, 2, 3, 4])
            base = best_n // (2 * k)
            target = max(2, base + 1 + rng.randrange(0, max(2, base // 10 + 1)))
            g = _sample_group(target, rng)
            if g is None:
                continue
            order, mul = g
            slice_end = min(deadline, now + max(3.0, 0.3 * remaining))
            res = _search(d, D, k, order, mul, rng, slice_end, 4000)
            if res is not None:
                consider(res[0], res[1])
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
